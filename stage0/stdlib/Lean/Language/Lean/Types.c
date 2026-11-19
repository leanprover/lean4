// Lean compiler output
// Module: Lean.Language.Lean.Types
// Imports: public import Lean.Elab.Command
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
lean_object* l_Lean_Language_Snapshot_transform(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTree_transform___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_finished___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_pushOpt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_pushOpt(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___closed__0 = (const lean_object*)&l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___closed__0 = (const lean_object*)&l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot = (const lean_object*)&l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__0 = (const lean_object*)&l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__0_value;
static const lean_closure_object l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__1 = (const lean_object*)&l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__1_value;
static const lean_closure_object l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTree_transform___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__2 = (const lean_object*)&l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__2_value;
static const lean_closure_object l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___lam__0___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__0_value),((lean_object*)&l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___closed__0_value),((lean_object*)&l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__1_value),((lean_object*)&l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__2_value)} };
static const lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__3 = (const lean_object*)&l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot = (const lean_object*)&l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot___closed__0 = (const lean_object*)&l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot = (const lean_object*)&l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___lam__0___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__1_value),((lean_object*)&l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot___closed__0_value)} };
static const lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__0 = (const lean_object*)&l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot = (const lean_object*)&l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lam__0___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__1_value),((lean_object*)&l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value)} };
static const lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___closed__0 = (const lean_object*)&l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot = (const lean_object*)&l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lam__0___boxed(lean_object*);
static lean_once_cell_t l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__0;
static const lean_closure_object l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1 = (const lean_object*)&l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_pushOpt___redArg(lean_object* v_a_x3f_1_, lean_object* v_as_2_){
_start:
{
if (lean_obj_tag(v_a_x3f_1_) == 0)
{
return v_as_2_;
}
else
{
lean_object* v_val_3_; lean_object* v___x_4_; 
v_val_3_ = lean_ctor_get(v_a_x3f_1_, 0);
lean_inc(v_val_3_);
lean_dec_ref_known(v_a_x3f_1_, 1);
v___x_4_ = lean_array_push(v_as_2_, v_val_3_);
return v___x_4_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_pushOpt(lean_object* v_00_u03b1_5_, lean_object* v_a_x3f_6_, lean_object* v_as_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_Language_Lean_pushOpt___redArg(v_a_x3f_6_, v_as_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0(lean_object* v_s_11_, lean_object* v___y_12_){
_start:
{
lean_object* v_toSnapshot_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_toSnapshot_13_ = lean_ctor_get(v_s_11_, 0);
lean_inc_ref(v_toSnapshot_13_);
lean_dec_ref(v_s_11_);
v___x_14_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_13_, v___y_12_);
v___x_15_ = ((lean_object*)(l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___closed__0));
v___x_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_14_);
lean_ctor_set(v___x_16_, 1, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___boxed(lean_object* v_s_17_, lean_object* v___y_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0(v_s_17_, v___y_18_);
lean_dec_ref(v___y_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___lam__0(lean_object* v___f_22_, lean_object* v___f_23_, lean_object* v___f_24_, lean_object* v___f_25_, lean_object* v_s_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_toSnapshot_28_; lean_object* v_elabSnap_29_; lean_object* v_resultSnap_30_; lean_object* v_infoTreeSnap_31_; lean_object* v_reportSnap_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v_toSnapshot_28_ = lean_ctor_get(v_s_26_, 0);
lean_inc_ref(v_toSnapshot_28_);
v_elabSnap_29_ = lean_ctor_get(v_s_26_, 1);
lean_inc_ref(v_elabSnap_29_);
v_resultSnap_30_ = lean_ctor_get(v_s_26_, 2);
lean_inc_ref(v_resultSnap_30_);
v_infoTreeSnap_31_ = lean_ctor_get(v_s_26_, 3);
lean_inc_ref(v_infoTreeSnap_31_);
v_reportSnap_32_ = lean_ctor_get(v_s_26_, 4);
lean_inc_ref(v_reportSnap_32_);
lean_dec_ref(v_s_26_);
v___x_33_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_28_, v___y_27_);
v___x_34_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_elabSnap_29_, v___f_22_, v___y_27_);
v___x_35_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_resultSnap_30_, v___f_23_, v___y_27_);
v___x_36_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_infoTreeSnap_31_, v___f_24_, v___y_27_);
v___x_37_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_reportSnap_32_, v___f_25_, v___y_27_);
v___x_38_ = lean_unsigned_to_nat(4u);
v___x_39_ = lean_mk_empty_array_with_capacity(v___x_38_);
v___x_40_ = lean_array_push(v___x_39_, v___x_34_);
v___x_41_ = lean_array_push(v___x_40_, v___x_35_);
v___x_42_ = lean_array_push(v___x_41_, v___x_36_);
v___x_43_ = lean_array_push(v___x_42_, v___x_37_);
v___x_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_33_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___lam__0___boxed(lean_object* v___f_45_, lean_object* v___f_46_, lean_object* v___f_47_, lean_object* v___f_48_, lean_object* v_s_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___lam__0(v___f_45_, v___f_46_, v___f_47_, v___f_48_, v_s_49_, v___y_50_);
lean_dec_ref(v___y_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0___lam__0(lean_object* v_s_61_, lean_object* v___y_62_){
_start:
{
lean_object* v_toSnapshotTreeM_63_; lean_object* v___x_64_; 
v_toSnapshotTreeM_63_ = lean_ctor_get(v_s_61_, 1);
lean_inc_ref(v_toSnapshotTreeM_63_);
lean_dec_ref(v_s_61_);
lean_inc_ref(v___y_62_);
v___x_64_ = lean_apply_1(v_toSnapshotTreeM_63_, v___y_62_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0___lam__0___boxed(lean_object* v_s_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0___lam__0(v_s_65_, v___y_66_);
lean_dec_ref(v___y_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0(lean_object* v_t_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___f_71_; lean_object* v___x_72_; 
v___f_71_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0___closed__0));
v___x_72_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_69_, v___f_71_, v_a_70_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0___boxed(lean_object* v_t_73_, lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0(v_t_73_, v_a_74_);
lean_dec_ref(v_a_74_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__1(lean_object* v_t_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___f_78_; lean_object* v___x_79_; 
v___f_78_ = ((lean_object*)(l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___closed__0));
v___x_79_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_76_, v___f_78_, v_a_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__1___boxed(lean_object* v_t_80_, lean_object* v_a_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__1(v_t_80_, v_a_81_);
lean_dec_ref(v_a_81_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2___lam__0(lean_object* v_s_83_, lean_object* v___y_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = l_Lean_Language_Snapshot_transform(v_s_83_, v___y_84_);
v___x_86_ = ((lean_object*)(l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___closed__0));
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2___lam__0___boxed(lean_object* v_s_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2___lam__0(v_s_88_, v___y_89_);
lean_dec_ref(v___y_89_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2(lean_object* v_t_92_, lean_object* v_a_93_){
_start:
{
lean_object* v___f_94_; lean_object* v___x_95_; 
v___f_94_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2___closed__0));
v___x_95_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_92_, v___f_94_, v_a_93_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2___boxed(lean_object* v_t_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2(v_t_96_, v_a_97_);
lean_dec_ref(v_a_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__3(lean_object* v_t_99_, lean_object* v_a_100_){
_start:
{
lean_object* v___f_101_; lean_object* v___x_102_; 
v___f_101_ = ((lean_object*)(l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__2));
v___x_102_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_99_, v___f_101_, v_a_100_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__3___boxed(lean_object* v_t_103_, lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__3(v_t_103_, v_a_104_);
lean_dec_ref(v_a_104_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___boxed(lean_object* v_s_106_, lean_object* v_a_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_s_106_, v_a_107_);
lean_dec_ref(v_a_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object* v_s_109_, lean_object* v_a_110_){
_start:
{
lean_object* v_elabSnap_111_; lean_object* v_toSnapshot_112_; lean_object* v_stx_113_; lean_object* v_nextCmdSnap_x3f_114_; lean_object* v_toSnapshot_115_; lean_object* v_elabSnap_116_; lean_object* v_resultSnap_117_; lean_object* v_infoTreeSnap_118_; lean_object* v_reportSnap_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___y_134_; 
v_elabSnap_111_ = lean_ctor_get(v_s_109_, 3);
lean_inc_ref(v_elabSnap_111_);
v_toSnapshot_112_ = lean_ctor_get(v_s_109_, 0);
lean_inc_ref(v_toSnapshot_112_);
v_stx_113_ = lean_ctor_get(v_s_109_, 1);
lean_inc(v_stx_113_);
v_nextCmdSnap_x3f_114_ = lean_ctor_get(v_s_109_, 4);
lean_inc(v_nextCmdSnap_x3f_114_);
lean_dec_ref(v_s_109_);
v_toSnapshot_115_ = lean_ctor_get(v_elabSnap_111_, 0);
lean_inc_ref(v_toSnapshot_115_);
v_elabSnap_116_ = lean_ctor_get(v_elabSnap_111_, 1);
lean_inc_ref(v_elabSnap_116_);
v_resultSnap_117_ = lean_ctor_get(v_elabSnap_111_, 2);
lean_inc_ref(v_resultSnap_117_);
v_infoTreeSnap_118_ = lean_ctor_get(v_elabSnap_111_, 3);
lean_inc_ref(v_infoTreeSnap_118_);
v_reportSnap_119_ = lean_ctor_get(v_elabSnap_111_, 4);
lean_inc_ref(v_reportSnap_119_);
lean_dec_ref(v_elabSnap_111_);
v___x_120_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_112_, v_a_110_);
v___x_121_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_115_, v_a_110_);
v___x_122_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0(v_elabSnap_116_, v_a_110_);
v___x_123_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__1(v_resultSnap_117_, v_a_110_);
v___x_124_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2(v_infoTreeSnap_118_, v_a_110_);
v___x_125_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__3(v_reportSnap_119_, v_a_110_);
v___x_126_ = lean_unsigned_to_nat(4u);
v___x_127_ = lean_mk_empty_array_with_capacity(v___x_126_);
v___x_128_ = lean_array_push(v___x_127_, v___x_122_);
v___x_129_ = lean_array_push(v___x_128_, v___x_123_);
v___x_130_ = lean_array_push(v___x_129_, v___x_124_);
v___x_131_ = lean_array_push(v___x_130_, v___x_125_);
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_121_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
if (lean_obj_tag(v_nextCmdSnap_x3f_114_) == 0)
{
lean_object* v___x_142_; 
v___x_142_ = lean_box(0);
v___y_134_ = v___x_142_;
goto v___jp_133_;
}
else
{
lean_object* v_val_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_152_; 
v_val_143_ = lean_ctor_get(v_nextCmdSnap_x3f_114_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v_nextCmdSnap_x3f_114_);
if (v_isSharedCheck_152_ == 0)
{
v___x_145_ = v_nextCmdSnap_x3f_114_;
v_isShared_146_ = v_isSharedCheck_152_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_val_143_);
lean_dec(v_nextCmdSnap_x3f_114_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_152_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_147_ = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___boxed), 2, 0);
v___x_148_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_val_143_, v___x_147_, v_a_110_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v___x_148_);
v___x_150_ = v___x_145_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_148_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
v___y_134_ = v___x_150_;
goto v___jp_133_;
}
}
}
v___jp_133_:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_135_, 0, v_stx_113_);
v___x_136_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_135_, v___x_132_);
v___x_137_ = lean_unsigned_to_nat(1u);
v___x_138_ = lean_mk_empty_array_with_capacity(v___x_137_);
v___x_139_ = lean_array_push(v___x_138_, v___x_136_);
v___x_140_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_134_, v___x_139_);
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_120_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___lam__0(lean_object* v___f_155_, lean_object* v___x_156_, lean_object* v_s_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_toSnapshot_159_; lean_object* v_metaSnap_160_; lean_object* v_result_x3f_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___y_165_; 
v_toSnapshot_159_ = lean_ctor_get(v_s_157_, 0);
lean_inc_ref(v_toSnapshot_159_);
v_metaSnap_160_ = lean_ctor_get(v_s_157_, 1);
lean_inc_ref(v_metaSnap_160_);
v_result_x3f_161_ = lean_ctor_get(v_s_157_, 2);
lean_inc(v_result_x3f_161_);
lean_dec_ref(v_s_157_);
v___x_162_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_159_, v___y_158_);
v___x_163_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_metaSnap_160_, v___f_155_, v___y_158_);
if (lean_obj_tag(v_result_x3f_161_) == 0)
{
lean_object* v___x_171_; 
lean_dec_ref(v___x_156_);
v___x_171_ = lean_box(0);
v___y_165_ = v___x_171_;
goto v___jp_164_;
}
else
{
lean_object* v_val_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_181_; 
v_val_172_ = lean_ctor_get(v_result_x3f_161_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v_result_x3f_161_);
if (v_isSharedCheck_181_ == 0)
{
v___x_174_ = v_result_x3f_161_;
v_isShared_175_ = v_isSharedCheck_181_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_val_172_);
lean_dec(v_result_x3f_161_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_181_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v_firstCmdSnap_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
v_firstCmdSnap_176_ = lean_ctor_get(v_val_172_, 1);
lean_inc_ref(v_firstCmdSnap_176_);
lean_dec(v_val_172_);
v___x_177_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_firstCmdSnap_176_, v___x_156_, v___y_158_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 0, v___x_177_);
v___x_179_ = v___x_174_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
v___y_165_ = v___x_179_;
goto v___jp_164_;
}
}
}
v___jp_164_:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_166_ = lean_unsigned_to_nat(1u);
v___x_167_ = lean_mk_empty_array_with_capacity(v___x_166_);
v___x_168_ = lean_array_push(v___x_167_, v___x_163_);
v___x_169_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_165_, v___x_168_);
v___x_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_162_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___lam__0___boxed(lean_object* v___f_182_, lean_object* v___x_183_, lean_object* v_s_184_, lean_object* v___y_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___lam__0(v___f_182_, v___x_183_, v_s_184_, v___y_185_);
lean_dec_ref(v___y_185_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lam__0(lean_object* v___f_191_, lean_object* v___x_192_, lean_object* v_s_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_toSnapshot_195_; lean_object* v_metaSnap_196_; lean_object* v_result_x3f_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___y_201_; 
v_toSnapshot_195_ = lean_ctor_get(v_s_193_, 0);
lean_inc_ref(v_toSnapshot_195_);
v_metaSnap_196_ = lean_ctor_get(v_s_193_, 1);
lean_inc_ref(v_metaSnap_196_);
v_result_x3f_197_ = lean_ctor_get(v_s_193_, 4);
lean_inc(v_result_x3f_197_);
lean_dec_ref(v_s_193_);
v___x_198_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_195_, v___y_194_);
v___x_199_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_metaSnap_196_, v___f_191_, v___y_194_);
if (lean_obj_tag(v_result_x3f_197_) == 0)
{
lean_object* v___x_207_; 
lean_dec_ref(v___x_192_);
v___x_207_ = lean_box(0);
v___y_201_ = v___x_207_;
goto v___jp_200_;
}
else
{
lean_object* v_val_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_217_; 
v_val_208_ = lean_ctor_get(v_result_x3f_197_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v_result_x3f_197_);
if (v_isSharedCheck_217_ == 0)
{
v___x_210_ = v_result_x3f_197_;
v_isShared_211_ = v_isSharedCheck_217_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_val_208_);
lean_dec(v_result_x3f_197_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_217_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v_processedSnap_212_; lean_object* v___x_213_; lean_object* v___x_215_; 
v_processedSnap_212_ = lean_ctor_get(v_val_208_, 1);
lean_inc_ref(v_processedSnap_212_);
lean_dec(v_val_208_);
v___x_213_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_processedSnap_212_, v___x_192_, v___y_194_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 0, v___x_213_);
v___x_215_ = v___x_210_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
v___y_201_ = v___x_215_;
goto v___jp_200_;
}
}
}
v___jp_200_:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_202_ = lean_unsigned_to_nat(1u);
v___x_203_ = lean_mk_empty_array_with_capacity(v___x_202_);
v___x_204_ = lean_array_push(v___x_203_, v___x_199_);
v___x_205_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_201_, v___x_204_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_198_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lam__0___boxed(lean_object* v___f_218_, lean_object* v___x_219_, lean_object* v_s_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lam__0(v___f_218_, v___x_219_, v_s_220_, v___y_221_);
lean_dec_ref(v___y_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lam__0(lean_object* v_x_227_){
_start:
{
lean_object* v_result_x3f_228_; 
v_result_x3f_228_ = lean_ctor_get(v_x_227_, 2);
lean_inc(v_result_x3f_228_);
return v_result_x3f_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lam__0___boxed(lean_object* v_x_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lam__0(v_x_229_);
lean_dec_ref(v_x_229_);
return v_res_230_;
}
}
static lean_object* _init_l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__0(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_box(0);
v___x_232_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_231_, v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(lean_object* v_snap_234_){
_start:
{
lean_object* v_result_x3f_235_; 
v_result_x3f_235_ = lean_ctor_get(v_snap_234_, 4);
lean_inc(v_result_x3f_235_);
lean_dec_ref(v_snap_234_);
if (lean_obj_tag(v_result_x3f_235_) == 0)
{
lean_object* v___x_236_; 
v___x_236_ = lean_obj_once(&l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__0, &l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__0_once, _init_l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__0);
return v___x_236_;
}
else
{
lean_object* v_val_237_; lean_object* v_processedSnap_238_; lean_object* v_stx_x3f_239_; lean_object* v_reportingRange_240_; lean_object* v___f_241_; uint8_t v___x_242_; lean_object* v___x_243_; 
v_val_237_ = lean_ctor_get(v_result_x3f_235_, 0);
lean_inc(v_val_237_);
lean_dec_ref_known(v_result_x3f_235_, 1);
v_processedSnap_238_ = lean_ctor_get(v_val_237_, 1);
lean_inc_ref(v_processedSnap_238_);
lean_dec(v_val_237_);
v_stx_x3f_239_ = lean_ctor_get(v_processedSnap_238_, 0);
lean_inc(v_stx_x3f_239_);
v_reportingRange_240_ = lean_ctor_get(v_processedSnap_238_, 1);
lean_inc(v_reportingRange_240_);
v___f_241_ = ((lean_object*)(l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1));
v___x_242_ = 1;
v___x_243_ = l_Lean_Language_SnapshotTask_map___redArg(v_processedSnap_238_, v___f_241_, v_stx_x3f_239_, v_reportingRange_240_, v___x_242_);
return v___x_243_;
}
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Language_Lean_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Language_Lean_Types(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Language_Lean_Types(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Language_Lean_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Language_Lean_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Language_Lean_Types(builtin);
}
#ifdef __cplusplus
}
#endif
