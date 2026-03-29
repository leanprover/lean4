// Lean compiler output
// Module: Lean.Elab.DeclarationRange
// Imports: public import Lean.Parser.Command
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDeclarationRanges___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_getDeclarationSelectionRef___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__0 = (const lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__0_value;
static const lean_string_object l_Lean_Elab_getDeclarationSelectionRef___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__1 = (const lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__1_value;
static const lean_string_object l_Lean_Elab_getDeclarationSelectionRef___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__2 = (const lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__2_value;
static const lean_string_object l_Lean_Elab_getDeclarationSelectionRef___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__3 = (const lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__3_value;
static const lean_ctor_object l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_getDeclarationSelectionRef___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__3_value),LEAN_SCALAR_PTR_LITERAL(37, 156, 84, 218, 244, 57, 142, 153)}};
static const lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__4 = (const lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationSelectionRef(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "example"};
static const lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 28, 224, 32, 144, 38, 51, 230)}};
static const lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___redArg___lam__0(lean_object* v_val_1_, lean_object* v_toPure_2_, lean_object* v_fileMap_3_){
_start:
{
lean_object* v_start_4_; lean_object* v_stop_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v_start_4_ = lean_ctor_get(v_val_1_, 0);
v_stop_5_ = lean_ctor_get(v_val_1_, 1);
v___x_6_ = l_Lean_DeclarationRange_ofStringPositions(v_fileMap_3_, v_start_4_, v_stop_5_);
v___x_7_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
v___x_8_ = lean_apply_2(v_toPure_2_, lean_box(0), v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___redArg___lam__0___boxed(lean_object* v_val_9_, lean_object* v_toPure_10_, lean_object* v_fileMap_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_Elab_getDeclarationRange_x3f___redArg___lam__0(v_val_9_, v_toPure_10_, v_fileMap_11_);
lean_dec_ref(v_val_9_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___redArg(lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_stx_15_){
_start:
{
lean_object* v_toApplicative_16_; lean_object* v_toBind_17_; lean_object* v_toPure_18_; uint8_t v___x_19_; lean_object* v___x_20_; 
v_toApplicative_16_ = lean_ctor_get(v_inst_13_, 0);
lean_inc_ref(v_toApplicative_16_);
v_toBind_17_ = lean_ctor_get(v_inst_13_, 1);
lean_inc(v_toBind_17_);
lean_dec_ref(v_inst_13_);
v_toPure_18_ = lean_ctor_get(v_toApplicative_16_, 1);
lean_inc(v_toPure_18_);
lean_dec_ref(v_toApplicative_16_);
v___x_19_ = 0;
v___x_20_ = l_Lean_Syntax_getRange_x3f(v_stx_15_, v___x_19_);
if (lean_obj_tag(v___x_20_) == 1)
{
lean_object* v_val_21_; lean_object* v___f_22_; lean_object* v___x_23_; 
v_val_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_val_21_);
lean_dec_ref(v___x_20_);
v___f_22_ = lean_alloc_closure((void*)(l_Lean_Elab_getDeclarationRange_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_22_, 0, v_val_21_);
lean_closure_set(v___f_22_, 1, v_toPure_18_);
v___x_23_ = lean_apply_4(v_toBind_17_, lean_box(0), lean_box(0), v_inst_14_, v___f_22_);
return v___x_23_;
}
else
{
lean_object* v___x_24_; lean_object* v___x_25_; 
lean_dec(v___x_20_);
lean_dec(v_toBind_17_);
lean_dec(v_inst_14_);
v___x_24_ = lean_box(0);
v___x_25_ = lean_apply_2(v_toPure_18_, lean_box(0), v___x_24_);
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___redArg___boxed(lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_stx_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Elab_getDeclarationRange_x3f___redArg(v_inst_26_, v_inst_27_, v_stx_28_);
lean_dec(v_stx_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f(lean_object* v_m_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_stx_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Elab_getDeclarationRange_x3f___redArg(v_inst_31_, v_inst_32_, v_stx_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___boxed(lean_object* v_m_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_stx_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_Elab_getDeclarationRange_x3f(v_m_35_, v_inst_36_, v_inst_37_, v_stx_38_);
lean_dec(v_stx_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationSelectionRef(lean_object* v_stx_49_){
_start:
{
lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_53_ = ((lean_object*)(l_Lean_Elab_getDeclarationSelectionRef___closed__4));
lean_inc(v_stx_49_);
v___x_54_ = l_Lean_Syntax_isOfKind(v_stx_49_, v___x_53_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_55_ = lean_unsigned_to_nat(1u);
v___x_56_ = l_Lean_Syntax_getArg(v_stx_49_, v___x_55_);
v___x_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = l_Lean_Syntax_getArg(v___x_56_, v___x_57_);
v___x_59_ = l_Lean_Syntax_isIdent(v___x_58_);
if (v___x_59_ == 0)
{
uint8_t v___x_60_; 
lean_dec(v___x_58_);
v___x_60_ = l_Lean_Syntax_isIdent(v___x_56_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; 
lean_dec(v___x_56_);
v___x_61_ = l_Lean_Syntax_getArg(v_stx_49_, v___x_57_);
lean_dec(v_stx_49_);
return v___x_61_;
}
else
{
lean_dec(v_stx_49_);
return v___x_56_;
}
}
else
{
lean_dec(v___x_56_);
lean_dec(v_stx_49_);
return v___x_58_;
}
}
else
{
lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_62_ = lean_unsigned_to_nat(3u);
v___x_63_ = l_Lean_Syntax_getArg(v_stx_49_, v___x_62_);
v___x_64_ = l_Lean_Syntax_isNone(v___x_63_);
if (v___x_64_ == 0)
{
if (v___x_54_ == 0)
{
lean_dec(v___x_63_);
goto v___jp_50_;
}
else
{
lean_object* v___x_65_; lean_object* v___x_66_; 
lean_dec(v_stx_49_);
v___x_65_ = lean_unsigned_to_nat(0u);
v___x_66_ = l_Lean_Syntax_getArg(v___x_63_, v___x_65_);
lean_dec(v___x_63_);
return v___x_66_;
}
}
else
{
lean_dec(v___x_63_);
goto v___jp_50_;
}
}
v___jp_50_:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_unsigned_to_nat(1u);
v___x_52_ = l_Lean_Syntax_getArg(v_stx_49_, v___x_51_);
lean_dec(v_stx_49_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__0(lean_object* v_val_67_, lean_object* v_x_68_){
_start:
{
if (lean_obj_tag(v_x_68_) == 0)
{
lean_inc_ref(v_val_67_);
return v_val_67_;
}
else
{
lean_object* v_val_69_; 
v_val_69_ = lean_ctor_get(v_x_68_, 0);
lean_inc(v_val_69_);
return v_val_69_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__0___boxed(lean_object* v_val_70_, lean_object* v_x_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__0(v_val_70_, v_x_71_);
lean_dec(v_x_71_);
lean_dec_ref(v_val_70_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__1(lean_object* v_val_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_declName_76_, lean_object* v_selectionRange_77_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_78_, 0, v_val_73_);
lean_ctor_set(v___x_78_, 1, v_selectionRange_77_);
v___x_79_ = l_Lean_addDeclarationRanges___redArg(v_inst_74_, v_inst_75_, v_declName_76_, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__2(lean_object* v_toFunctor_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_declName_83_, lean_object* v_inst_84_, lean_object* v_selectionRangeStx_85_, lean_object* v_toBind_86_, lean_object* v_toPure_87_, lean_object* v_____x_88_){
_start:
{
if (lean_obj_tag(v_____x_88_) == 1)
{
lean_object* v_val_89_; lean_object* v_map_90_; lean_object* v___f_91_; lean_object* v___f_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
lean_dec(v_toPure_87_);
v_val_89_ = lean_ctor_get(v_____x_88_, 0);
lean_inc_n(v_val_89_, 2);
lean_dec_ref(v_____x_88_);
v_map_90_ = lean_ctor_get(v_toFunctor_80_, 0);
lean_inc(v_map_90_);
lean_dec_ref(v_toFunctor_80_);
v___f_91_ = lean_alloc_closure((void*)(l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_91_, 0, v_val_89_);
lean_inc_ref(v_inst_81_);
v___f_92_ = lean_alloc_closure((void*)(l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__1), 5, 4);
lean_closure_set(v___f_92_, 0, v_val_89_);
lean_closure_set(v___f_92_, 1, v_inst_81_);
lean_closure_set(v___f_92_, 2, v_inst_82_);
lean_closure_set(v___f_92_, 3, v_declName_83_);
v___x_93_ = l_Lean_Elab_getDeclarationRange_x3f___redArg(v_inst_81_, v_inst_84_, v_selectionRangeStx_85_);
v___x_94_ = lean_apply_4(v_map_90_, lean_box(0), lean_box(0), v___f_91_, v___x_93_);
v___x_95_ = lean_apply_4(v_toBind_86_, lean_box(0), lean_box(0), v___x_94_, v___f_92_);
return v___x_95_;
}
else
{
lean_object* v___x_96_; lean_object* v___x_97_; 
lean_dec(v_____x_88_);
lean_dec(v_toBind_86_);
lean_dec(v_inst_84_);
lean_dec(v_declName_83_);
lean_dec_ref(v_inst_82_);
lean_dec_ref(v_inst_81_);
lean_dec_ref(v_toFunctor_80_);
v___x_96_ = lean_box(0);
v___x_97_ = lean_apply_2(v_toPure_87_, lean_box(0), v___x_96_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__2___boxed(lean_object* v_toFunctor_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_declName_101_, lean_object* v_inst_102_, lean_object* v_selectionRangeStx_103_, lean_object* v_toBind_104_, lean_object* v_toPure_105_, lean_object* v_____x_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__2(v_toFunctor_98_, v_inst_99_, v_inst_100_, v_declName_101_, v_inst_102_, v_selectionRangeStx_103_, v_toBind_104_, v_toPure_105_, v_____x_106_);
lean_dec(v_selectionRangeStx_103_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg(lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_declName_111_, lean_object* v_rangeStx_112_, lean_object* v_selectionRangeStx_113_){
_start:
{
lean_object* v_toApplicative_114_; lean_object* v_toBind_115_; lean_object* v_toFunctor_116_; lean_object* v_toPure_117_; lean_object* v___x_118_; lean_object* v___f_119_; lean_object* v___x_120_; 
v_toApplicative_114_ = lean_ctor_get(v_inst_108_, 0);
v_toBind_115_ = lean_ctor_get(v_inst_108_, 1);
lean_inc_n(v_toBind_115_, 2);
v_toFunctor_116_ = lean_ctor_get(v_toApplicative_114_, 0);
lean_inc_ref(v_toFunctor_116_);
v_toPure_117_ = lean_ctor_get(v_toApplicative_114_, 1);
lean_inc(v_toPure_117_);
lean_inc(v_inst_110_);
lean_inc_ref(v_inst_108_);
v___x_118_ = l_Lean_Elab_getDeclarationRange_x3f___redArg(v_inst_108_, v_inst_110_, v_rangeStx_112_);
v___f_119_ = lean_alloc_closure((void*)(l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_119_, 0, v_toFunctor_116_);
lean_closure_set(v___f_119_, 1, v_inst_108_);
lean_closure_set(v___f_119_, 2, v_inst_109_);
lean_closure_set(v___f_119_, 3, v_declName_111_);
lean_closure_set(v___f_119_, 4, v_inst_110_);
lean_closure_set(v___f_119_, 5, v_selectionRangeStx_113_);
lean_closure_set(v___f_119_, 6, v_toBind_115_);
lean_closure_set(v___f_119_, 7, v_toPure_117_);
v___x_120_ = lean_apply_4(v_toBind_115_, lean_box(0), lean_box(0), v___x_118_, v___f_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___boxed(lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_declName_124_, lean_object* v_rangeStx_125_, lean_object* v_selectionRangeStx_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Elab_addDeclarationRangesFromSyntax___redArg(v_inst_121_, v_inst_122_, v_inst_123_, v_declName_124_, v_rangeStx_125_, v_selectionRangeStx_126_);
lean_dec(v_rangeStx_125_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax(lean_object* v_m_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_declName_132_, lean_object* v_rangeStx_133_, lean_object* v_selectionRangeStx_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Elab_addDeclarationRangesFromSyntax___redArg(v_inst_129_, v_inst_130_, v_inst_131_, v_declName_132_, v_rangeStx_133_, v_selectionRangeStx_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___boxed(lean_object* v_m_136_, lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_declName_140_, lean_object* v_rangeStx_141_, lean_object* v_selectionRangeStx_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Elab_addDeclarationRangesFromSyntax(v_m_136_, v_inst_137_, v_inst_138_, v_inst_139_, v_declName_140_, v_rangeStx_141_, v_selectionRangeStx_142_);
lean_dec(v_rangeStx_141_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin___redArg(lean_object* v_inst_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_declName_156_, lean_object* v_modsStx_157_, lean_object* v_declStx_158_){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
lean_inc(v_declStx_158_);
v___x_159_ = l_Lean_Syntax_getKind(v_declStx_158_);
v___x_160_ = ((lean_object*)(l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1));
v___x_161_ = lean_name_eq(v___x_159_, v___x_160_);
lean_dec(v___x_159_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v_stx_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_162_ = lean_unsigned_to_nat(2u);
v___x_163_ = lean_mk_empty_array_with_capacity(v___x_162_);
v___x_164_ = lean_array_push(v___x_163_, v_modsStx_157_);
lean_inc(v_declStx_158_);
v___x_165_ = lean_array_push(v___x_164_, v_declStx_158_);
v___x_166_ = ((lean_object*)(l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__3));
v___x_167_ = lean_box(2);
v_stx_168_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_stx_168_, 0, v___x_167_);
lean_ctor_set(v_stx_168_, 1, v___x_166_);
lean_ctor_set(v_stx_168_, 2, v___x_165_);
v___x_169_ = l_Lean_Elab_getDeclarationSelectionRef(v_declStx_158_);
v___x_170_ = l_Lean_Elab_addDeclarationRangesFromSyntax___redArg(v_inst_153_, v_inst_154_, v_inst_155_, v_declName_156_, v_stx_168_, v___x_169_);
lean_dec_ref(v_stx_168_);
return v___x_170_;
}
else
{
lean_object* v_toApplicative_171_; lean_object* v_toPure_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec(v_declStx_158_);
lean_dec(v_modsStx_157_);
lean_dec(v_declName_156_);
lean_dec(v_inst_155_);
lean_dec_ref(v_inst_154_);
v_toApplicative_171_ = lean_ctor_get(v_inst_153_, 0);
lean_inc_ref(v_toApplicative_171_);
lean_dec_ref(v_inst_153_);
v_toPure_172_ = lean_ctor_get(v_toApplicative_171_, 1);
lean_inc(v_toPure_172_);
lean_dec_ref(v_toApplicative_171_);
v___x_173_ = lean_box(0);
v___x_174_ = lean_apply_2(v_toPure_172_, lean_box(0), v___x_173_);
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin(lean_object* v_m_175_, lean_object* v_inst_176_, lean_object* v_inst_177_, lean_object* v_inst_178_, lean_object* v_declName_179_, lean_object* v_modsStx_180_, lean_object* v_declStx_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Lean_Elab_addDeclarationRangesForBuiltin___redArg(v_inst_176_, v_inst_177_, v_inst_178_, v_declName_179_, v_modsStx_180_, v_declStx_181_);
return v___x_182_;
}
}
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DeclarationRange(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_DeclarationRange(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DeclarationRange(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_DeclarationRange(builtin);
}
#ifdef __cplusplus
}
#endif
