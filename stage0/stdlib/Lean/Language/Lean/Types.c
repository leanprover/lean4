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
lean_object* v_toSnapshot_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_22_; 
v_toSnapshot_13_ = lean_ctor_get(v_s_11_, 0);
v_isSharedCheck_22_ = !lean_is_exclusive(v_s_11_);
if (v_isSharedCheck_22_ == 0)
{
lean_object* v_unused_23_; 
v_unused_23_ = lean_ctor_get(v_s_11_, 1);
lean_dec(v_unused_23_);
v___x_15_ = v_s_11_;
v_isShared_16_ = v_isSharedCheck_22_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_toSnapshot_13_);
lean_dec(v_s_11_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_22_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_20_; 
v___x_17_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_13_, v___y_12_);
v___x_18_ = ((lean_object*)(l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___closed__0));
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 1, v___x_18_);
lean_ctor_set(v___x_15_, 0, v___x_17_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_17_);
lean_ctor_set(v_reuseFailAlloc_21_, 1, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___boxed(lean_object* v_s_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0(v_s_24_, v___y_25_);
lean_dec_ref(v___y_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___lam__0(lean_object* v___f_29_, lean_object* v___f_30_, lean_object* v___f_31_, lean_object* v___f_32_, lean_object* v_s_33_, lean_object* v___y_34_){
_start:
{
lean_object* v_toSnapshot_35_; lean_object* v_elabSnap_36_; lean_object* v_resultSnap_37_; lean_object* v_infoTreeSnap_38_; lean_object* v_reportSnap_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v_toSnapshot_35_ = lean_ctor_get(v_s_33_, 0);
lean_inc_ref(v_toSnapshot_35_);
v_elabSnap_36_ = lean_ctor_get(v_s_33_, 1);
lean_inc_ref(v_elabSnap_36_);
v_resultSnap_37_ = lean_ctor_get(v_s_33_, 2);
lean_inc_ref(v_resultSnap_37_);
v_infoTreeSnap_38_ = lean_ctor_get(v_s_33_, 3);
lean_inc_ref(v_infoTreeSnap_38_);
v_reportSnap_39_ = lean_ctor_get(v_s_33_, 4);
lean_inc_ref(v_reportSnap_39_);
lean_dec_ref(v_s_33_);
v___x_40_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_35_, v___y_34_);
v___x_41_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_elabSnap_36_, v___f_29_, v___y_34_);
v___x_42_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_resultSnap_37_, v___f_30_, v___y_34_);
v___x_43_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_infoTreeSnap_38_, v___f_31_, v___y_34_);
v___x_44_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_reportSnap_39_, v___f_32_, v___y_34_);
v___x_45_ = lean_unsigned_to_nat(4u);
v___x_46_ = lean_mk_empty_array_with_capacity(v___x_45_);
v___x_47_ = lean_array_push(v___x_46_, v___x_41_);
v___x_48_ = lean_array_push(v___x_47_, v___x_42_);
v___x_49_ = lean_array_push(v___x_48_, v___x_43_);
v___x_50_ = lean_array_push(v___x_49_, v___x_44_);
v___x_51_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_40_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___lam__0___boxed(lean_object* v___f_52_, lean_object* v___f_53_, lean_object* v___f_54_, lean_object* v___f_55_, lean_object* v_s_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___lam__0(v___f_52_, v___f_53_, v___f_54_, v___f_55_, v_s_56_, v___y_57_);
lean_dec_ref(v___y_57_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0___lam__0(lean_object* v_s_68_, lean_object* v___y_69_){
_start:
{
lean_object* v_toSnapshotTreeM_70_; lean_object* v___x_71_; 
v_toSnapshotTreeM_70_ = lean_ctor_get(v_s_68_, 1);
lean_inc_ref(v_toSnapshotTreeM_70_);
lean_dec_ref(v_s_68_);
lean_inc_ref(v___y_69_);
v___x_71_ = lean_apply_1(v_toSnapshotTreeM_70_, v___y_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0___lam__0___boxed(lean_object* v_s_72_, lean_object* v___y_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0___lam__0(v_s_72_, v___y_73_);
lean_dec_ref(v___y_73_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0(lean_object* v_t_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___f_78_; lean_object* v___x_79_; 
v___f_78_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0___closed__0));
v___x_79_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_76_, v___f_78_, v_a_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0___boxed(lean_object* v_t_80_, lean_object* v_a_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0(v_t_80_, v_a_81_);
lean_dec_ref(v_a_81_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__1(lean_object* v_t_83_, lean_object* v_a_84_){
_start:
{
lean_object* v___f_85_; lean_object* v___x_86_; 
v___f_85_ = ((lean_object*)(l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___closed__0));
v___x_86_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_83_, v___f_85_, v_a_84_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__1___boxed(lean_object* v_t_87_, lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__1(v_t_87_, v_a_88_);
lean_dec_ref(v_a_88_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2___lam__0(lean_object* v_s_90_, lean_object* v___y_91_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = l_Lean_Language_Snapshot_transform(v_s_90_, v___y_91_);
v___x_93_ = ((lean_object*)(l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___closed__0));
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_92_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2___lam__0___boxed(lean_object* v_s_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2___lam__0(v_s_95_, v___y_96_);
lean_dec_ref(v___y_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2(lean_object* v_t_99_, lean_object* v_a_100_){
_start:
{
lean_object* v___f_101_; lean_object* v___x_102_; 
v___f_101_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2___closed__0));
v___x_102_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_99_, v___f_101_, v_a_100_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2___boxed(lean_object* v_t_103_, lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2(v_t_103_, v_a_104_);
lean_dec_ref(v_a_104_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__3(lean_object* v_t_106_, lean_object* v_a_107_){
_start:
{
lean_object* v___f_108_; lean_object* v___x_109_; 
v___f_108_ = ((lean_object*)(l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__2));
v___x_109_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_106_, v___f_108_, v_a_107_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__3___boxed(lean_object* v_t_110_, lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__3(v_t_110_, v_a_111_);
lean_dec_ref(v_a_111_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___boxed(lean_object* v_s_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_s_113_, v_a_114_);
lean_dec_ref(v_a_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object* v_s_116_, lean_object* v_a_117_){
_start:
{
lean_object* v_elabSnap_118_; lean_object* v_toSnapshot_119_; lean_object* v_stx_120_; lean_object* v_nextCmdSnap_x3f_121_; lean_object* v_toSnapshot_122_; lean_object* v_elabSnap_123_; lean_object* v_resultSnap_124_; lean_object* v_infoTreeSnap_125_; lean_object* v_reportSnap_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___y_141_; 
v_elabSnap_118_ = lean_ctor_get(v_s_116_, 3);
lean_inc_ref(v_elabSnap_118_);
v_toSnapshot_119_ = lean_ctor_get(v_s_116_, 0);
lean_inc_ref(v_toSnapshot_119_);
v_stx_120_ = lean_ctor_get(v_s_116_, 1);
lean_inc(v_stx_120_);
v_nextCmdSnap_x3f_121_ = lean_ctor_get(v_s_116_, 4);
lean_inc(v_nextCmdSnap_x3f_121_);
lean_dec_ref(v_s_116_);
v_toSnapshot_122_ = lean_ctor_get(v_elabSnap_118_, 0);
lean_inc_ref(v_toSnapshot_122_);
v_elabSnap_123_ = lean_ctor_get(v_elabSnap_118_, 1);
lean_inc_ref(v_elabSnap_123_);
v_resultSnap_124_ = lean_ctor_get(v_elabSnap_118_, 2);
lean_inc_ref(v_resultSnap_124_);
v_infoTreeSnap_125_ = lean_ctor_get(v_elabSnap_118_, 3);
lean_inc_ref(v_infoTreeSnap_125_);
v_reportSnap_126_ = lean_ctor_get(v_elabSnap_118_, 4);
lean_inc_ref(v_reportSnap_126_);
lean_dec_ref(v_elabSnap_118_);
v___x_127_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_119_, v_a_117_);
v___x_128_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_122_, v_a_117_);
v___x_129_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__0(v_elabSnap_123_, v_a_117_);
v___x_130_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__1(v_resultSnap_124_, v_a_117_);
v___x_131_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__2(v_infoTreeSnap_125_, v_a_117_);
v___x_132_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go_spec__3(v_reportSnap_126_, v_a_117_);
v___x_133_ = lean_unsigned_to_nat(4u);
v___x_134_ = lean_mk_empty_array_with_capacity(v___x_133_);
v___x_135_ = lean_array_push(v___x_134_, v___x_129_);
v___x_136_ = lean_array_push(v___x_135_, v___x_130_);
v___x_137_ = lean_array_push(v___x_136_, v___x_131_);
v___x_138_ = lean_array_push(v___x_137_, v___x_132_);
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_128_);
lean_ctor_set(v___x_139_, 1, v___x_138_);
if (lean_obj_tag(v_nextCmdSnap_x3f_121_) == 0)
{
lean_object* v___x_149_; 
v___x_149_ = lean_box(0);
v___y_141_ = v___x_149_;
goto v___jp_140_;
}
else
{
lean_object* v_val_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_159_; 
v_val_150_ = lean_ctor_get(v_nextCmdSnap_x3f_121_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v_nextCmdSnap_x3f_121_);
if (v_isSharedCheck_159_ == 0)
{
v___x_152_ = v_nextCmdSnap_x3f_121_;
v_isShared_153_ = v_isSharedCheck_159_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_val_150_);
lean_dec(v_nextCmdSnap_x3f_121_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_159_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_154_ = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___boxed), 2, 0);
v___x_155_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_val_150_, v___x_154_, v_a_117_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_155_);
v___x_157_ = v___x_152_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
v___y_141_ = v___x_157_;
goto v___jp_140_;
}
}
}
v___jp_140_:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_142_, 0, v_stx_120_);
v___x_143_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_142_, v___x_139_);
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = lean_mk_empty_array_with_capacity(v___x_144_);
v___x_146_ = lean_array_push(v___x_145_, v___x_143_);
v___x_147_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_141_, v___x_146_);
v___x_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_127_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___lam__0(lean_object* v___f_162_, lean_object* v___x_163_, lean_object* v_s_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_toSnapshot_166_; lean_object* v_metaSnap_167_; lean_object* v_result_x3f_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___y_172_; 
v_toSnapshot_166_ = lean_ctor_get(v_s_164_, 0);
lean_inc_ref(v_toSnapshot_166_);
v_metaSnap_167_ = lean_ctor_get(v_s_164_, 1);
lean_inc_ref(v_metaSnap_167_);
v_result_x3f_168_ = lean_ctor_get(v_s_164_, 2);
lean_inc(v_result_x3f_168_);
lean_dec_ref(v_s_164_);
v___x_169_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_166_, v___y_165_);
v___x_170_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_metaSnap_167_, v___f_162_, v___y_165_);
if (lean_obj_tag(v_result_x3f_168_) == 0)
{
lean_object* v___x_178_; 
lean_dec_ref(v___x_163_);
v___x_178_ = lean_box(0);
v___y_172_ = v___x_178_;
goto v___jp_171_;
}
else
{
lean_object* v_val_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_188_; 
v_val_179_ = lean_ctor_get(v_result_x3f_168_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v_result_x3f_168_);
if (v_isSharedCheck_188_ == 0)
{
v___x_181_ = v_result_x3f_168_;
v_isShared_182_ = v_isSharedCheck_188_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_val_179_);
lean_dec(v_result_x3f_168_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_188_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v_firstCmdSnap_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
v_firstCmdSnap_183_ = lean_ctor_get(v_val_179_, 1);
lean_inc_ref(v_firstCmdSnap_183_);
lean_dec(v_val_179_);
v___x_184_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_firstCmdSnap_183_, v___x_163_, v___y_165_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_184_);
v___x_186_ = v___x_181_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
v___y_172_ = v___x_186_;
goto v___jp_171_;
}
}
}
v___jp_171_:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = lean_mk_empty_array_with_capacity(v___x_173_);
v___x_175_ = lean_array_push(v___x_174_, v___x_170_);
v___x_176_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_172_, v___x_175_);
v___x_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_169_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___lam__0___boxed(lean_object* v___f_189_, lean_object* v___x_190_, lean_object* v_s_191_, lean_object* v___y_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___lam__0(v___f_189_, v___x_190_, v_s_191_, v___y_192_);
lean_dec_ref(v___y_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lam__0(lean_object* v___f_198_, lean_object* v___x_199_, lean_object* v_s_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_toSnapshot_202_; lean_object* v_metaSnap_203_; lean_object* v_result_x3f_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___y_208_; 
v_toSnapshot_202_ = lean_ctor_get(v_s_200_, 0);
lean_inc_ref(v_toSnapshot_202_);
v_metaSnap_203_ = lean_ctor_get(v_s_200_, 1);
lean_inc_ref(v_metaSnap_203_);
v_result_x3f_204_ = lean_ctor_get(v_s_200_, 4);
lean_inc(v_result_x3f_204_);
lean_dec_ref(v_s_200_);
v___x_205_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_202_, v___y_201_);
v___x_206_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_metaSnap_203_, v___f_198_, v___y_201_);
if (lean_obj_tag(v_result_x3f_204_) == 0)
{
lean_object* v___x_214_; 
lean_dec_ref(v___x_199_);
v___x_214_ = lean_box(0);
v___y_208_ = v___x_214_;
goto v___jp_207_;
}
else
{
lean_object* v_val_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_224_; 
v_val_215_ = lean_ctor_get(v_result_x3f_204_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v_result_x3f_204_);
if (v_isSharedCheck_224_ == 0)
{
v___x_217_ = v_result_x3f_204_;
v_isShared_218_ = v_isSharedCheck_224_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_val_215_);
lean_dec(v_result_x3f_204_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_224_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v_processedSnap_219_; lean_object* v___x_220_; lean_object* v___x_222_; 
v_processedSnap_219_ = lean_ctor_get(v_val_215_, 1);
lean_inc_ref(v_processedSnap_219_);
lean_dec(v_val_215_);
v___x_220_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_processedSnap_219_, v___x_199_, v___y_201_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_220_);
v___x_222_ = v___x_217_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
v___y_208_ = v___x_222_;
goto v___jp_207_;
}
}
}
v___jp_207_:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_209_ = lean_unsigned_to_nat(1u);
v___x_210_ = lean_mk_empty_array_with_capacity(v___x_209_);
v___x_211_ = lean_array_push(v___x_210_, v___x_206_);
v___x_212_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_208_, v___x_211_);
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_205_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lam__0___boxed(lean_object* v___f_225_, lean_object* v___x_226_, lean_object* v_s_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lam__0(v___f_225_, v___x_226_, v_s_227_, v___y_228_);
lean_dec_ref(v___y_228_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lam__0(lean_object* v_x_234_){
_start:
{
lean_object* v_result_x3f_235_; 
v_result_x3f_235_ = lean_ctor_get(v_x_234_, 2);
lean_inc(v_result_x3f_235_);
return v_result_x3f_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lam__0___boxed(lean_object* v_x_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lam__0(v_x_236_);
lean_dec_ref(v_x_236_);
return v_res_237_;
}
}
static lean_object* _init_l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__0(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_box(0);
v___x_239_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_238_, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(lean_object* v_snap_241_){
_start:
{
lean_object* v_result_x3f_242_; 
v_result_x3f_242_ = lean_ctor_get(v_snap_241_, 4);
lean_inc(v_result_x3f_242_);
lean_dec_ref(v_snap_241_);
if (lean_obj_tag(v_result_x3f_242_) == 0)
{
lean_object* v___x_243_; 
v___x_243_ = lean_obj_once(&l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__0, &l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__0_once, _init_l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__0);
return v___x_243_;
}
else
{
lean_object* v_val_244_; lean_object* v_processedSnap_245_; lean_object* v_stx_x3f_246_; lean_object* v_reportingRange_247_; lean_object* v___f_248_; uint8_t v___x_249_; lean_object* v___x_250_; 
v_val_244_ = lean_ctor_get(v_result_x3f_242_, 0);
lean_inc(v_val_244_);
lean_dec_ref_known(v_result_x3f_242_, 1);
v_processedSnap_245_ = lean_ctor_get(v_val_244_, 1);
lean_inc_ref(v_processedSnap_245_);
lean_dec(v_val_244_);
v_stx_x3f_246_ = lean_ctor_get(v_processedSnap_245_, 0);
lean_inc(v_stx_x3f_246_);
v_reportingRange_247_ = lean_ctor_get(v_processedSnap_245_, 1);
lean_inc(v_reportingRange_247_);
v___f_248_ = ((lean_object*)(l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1));
v___x_249_ = 1;
v___x_250_ = l_Lean_Language_SnapshotTask_map___redArg(v_processedSnap_245_, v___f_248_, v_stx_x3f_246_, v_reportingRange_247_, v___x_249_);
return v___x_250_;
}
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Language_Lean_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
