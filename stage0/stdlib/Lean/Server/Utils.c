// Lean compiler output
// Module: Lean.Server.Utils
// Imports: public import Init.System.Uri public import Lean.Data.Lsp.Communication public import Lean.Data.Lsp.Diagnostics public import Lean.Data.Lsp.Extra public import Lean.Elab.InfoTree.Util
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_crlfToLf(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_String_toFileMap(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_System_Uri_fileUriToPath_x3f(lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_getSrcSearchPath();
lean_object* l_Lean_searchModuleNameOfFileName(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_Lean_SearchPath_findModuleWithExt(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*);
lean_object* l_System_Uri_pathToUri(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_throwServerError___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_throwServerError___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_throwServerError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_throwServerError___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___lam__0(lean_object*, lean_object*, uint8_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___lam__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_withPrefix___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_withPrefix___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_withPrefix___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_withPrefix___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_withPrefix(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_instInhabitedDocumentMeta_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Server_instInhabitedDocumentMeta_default___closed__0 = (const lean_object*)&l_Lean_Server_instInhabitedDocumentMeta_default___closed__0_value;
static lean_once_cell_t l_Lean_Server_instInhabitedDocumentMeta_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instInhabitedDocumentMeta_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedDocumentMeta_default;
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedDocumentMeta;
LEAN_EXPORT lean_object* l_Lean_Server_DocumentMeta_mkInputContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_replaceLspRange(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_replaceLspRange___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_applyDocumentChange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_applyDocumentChange___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_foldDocumentChanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_foldDocumentChanges___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Server_mkPublishDiagnosticsNotification_spec__0(lean_object*);
static const lean_string_object l_Lean_Server_mkPublishDiagnosticsNotification___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "textDocument/publishDiagnostics"};
static const lean_object* l_Lean_Server_mkPublishDiagnosticsNotification___closed__0 = (const lean_object*)&l_Lean_Server_mkPublishDiagnosticsNotification___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_mkPublishDiagnosticsNotification(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_mkFileProgressNotification___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "$/lean/fileProgress"};
static const lean_object* l_Lean_Server_mkFileProgressNotification___closed__0 = (const lean_object*)&l_Lean_Server_mkFileProgressNotification___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressNotification(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressNotification___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressAtPosNotification(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressAtPosNotification___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_mkFileProgressDoneNotification___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_mkFileProgressDoneNotification___closed__0 = (const lean_object*)&l_Lean_Server_mkFileProgressDoneNotification___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressDoneNotification(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressDoneNotification___boxed(lean_object*);
static const lean_string_object l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "workspace/applyEdit"};
static const lean_object* l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0 = (const lean_object*)&l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0_value;
static const lean_ctor_object l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0_value)}};
static const lean_object* l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1 = (const lean_object*)&l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_mkApplyWorkspaceEditRequest(lean_object*);
static const lean_string_object l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "external:"};
static const lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0 = (const lean_object*)&l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f(lean_object*);
static const lean_string_object l_Lean_Server_documentUriFromModule_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_Server_documentUriFromModule_x3f___closed__0 = (const lean_object*)&l_Lean_Server_documentUriFromModule_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_documentUriFromModule_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_documentUriFromModule_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Server_moduleFromDocumentUri___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_documentUriFromModule_x3f___closed__0_value)}};
static const lean_object* l_Lean_Server_moduleFromDocumentUri___closed__0 = (const lean_object*)&l_Lean_Server_moduleFromDocumentUri___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_moduleFromDocumentUri(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_moduleFromDocumentUri___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_toLspRange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_throwServerError___redArg(lean_object* v_err_1_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_mk_io_user_error(v_err_1_);
v___x_4_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4_, 0, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_throwServerError___redArg___boxed(lean_object* v_err_5_, lean_object* v_a_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lean_IO_throwServerError___redArg(v_err_5_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_throwServerError(lean_object* v_00_u03b1_8_, lean_object* v_err_9_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = l_Lean_IO_throwServerError___redArg(v_err_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_throwServerError___boxed(lean_object* v_00_u03b1_12_, lean_object* v_err_13_, lean_object* v_a_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_IO_throwServerError(v_00_u03b1_12_, v_err_13_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___lam__0(lean_object* v_read_16_, lean_object* v_b_17_, uint8_t v_flushEagerly_18_, size_t v_sz_19_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_box_usize(v_sz_19_);
v___x_22_ = lean_apply_2(v_read_16_, v___x_21_, lean_box(0));
if (lean_obj_tag(v___x_22_) == 0)
{
lean_object* v_a_23_; lean_object* v_flush_24_; lean_object* v_write_25_; lean_object* v___x_26_; 
v_a_23_ = lean_ctor_get(v___x_22_, 0);
lean_inc_n(v_a_23_, 2);
lean_dec_ref_known(v___x_22_, 1);
v_flush_24_ = lean_ctor_get(v_b_17_, 0);
lean_inc_ref(v_flush_24_);
v_write_25_ = lean_ctor_get(v_b_17_, 2);
lean_inc_ref(v_write_25_);
lean_dec_ref(v_b_17_);
v___x_26_ = lean_apply_2(v_write_25_, v_a_23_, lean_box(0));
if (lean_obj_tag(v___x_26_) == 0)
{
lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_50_; 
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_26_);
if (v_isSharedCheck_50_ == 0)
{
lean_object* v_unused_51_; 
v_unused_51_ = lean_ctor_get(v___x_26_, 0);
lean_dec(v_unused_51_);
v___x_28_ = v___x_26_;
v_isShared_29_ = v_isSharedCheck_50_;
goto v_resetjp_27_;
}
else
{
lean_dec(v___x_26_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_50_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
if (v_flushEagerly_18_ == 0)
{
lean_object* v___x_31_; 
lean_dec_ref(v_flush_24_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 0, v_a_23_);
v___x_31_ = v___x_28_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v_a_23_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
else
{
lean_object* v___x_33_; 
lean_del_object(v___x_28_);
v___x_33_ = lean_apply_1(v_flush_24_, lean_box(0));
if (lean_obj_tag(v___x_33_) == 0)
{
lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_40_; 
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_40_ == 0)
{
lean_object* v_unused_41_; 
v_unused_41_ = lean_ctor_get(v___x_33_, 0);
lean_dec(v_unused_41_);
v___x_35_ = v___x_33_;
v_isShared_36_ = v_isSharedCheck_40_;
goto v_resetjp_34_;
}
else
{
lean_dec(v___x_33_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_40_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_38_; 
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 0, v_a_23_);
v___x_38_ = v___x_35_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_a_23_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
else
{
lean_object* v_a_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_49_; 
lean_dec(v_a_23_);
v_a_42_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_49_ == 0)
{
v___x_44_ = v___x_33_;
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_a_42_);
lean_dec(v___x_33_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_47_; 
if (v_isShared_45_ == 0)
{
v___x_47_ = v___x_44_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_a_42_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
}
}
}
else
{
lean_object* v_a_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_59_; 
lean_dec_ref(v_flush_24_);
lean_dec(v_a_23_);
v_a_52_ = lean_ctor_get(v___x_26_, 0);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_26_);
if (v_isSharedCheck_59_ == 0)
{
v___x_54_ = v___x_26_;
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_a_52_);
lean_dec(v___x_26_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_57_; 
if (v_isShared_55_ == 0)
{
v___x_57_ = v___x_54_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_a_52_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
}
else
{
lean_dec_ref(v_b_17_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___lam__0___boxed(lean_object* v_read_60_, lean_object* v_b_61_, lean_object* v_flushEagerly_62_, lean_object* v_sz_63_, lean_object* v___y_64_){
_start:
{
uint8_t v_flushEagerly_boxed_65_; size_t v_sz_boxed_66_; lean_object* v_res_67_; 
v_flushEagerly_boxed_65_ = lean_unbox(v_flushEagerly_62_);
v_sz_boxed_66_ = lean_unbox_usize(v_sz_63_);
lean_dec(v_sz_63_);
v_res_67_ = l_Lean_IO_FS_Stream_chainRight___lam__0(v_read_60_, v_b_61_, v_flushEagerly_boxed_65_, v_sz_boxed_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___lam__1(lean_object* v_getLine_68_, lean_object* v_b_69_, uint8_t v_flushEagerly_70_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_apply_1(v_getLine_68_, lean_box(0));
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v_flush_74_; lean_object* v_putStr_75_; lean_object* v___x_76_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc_n(v_a_73_, 2);
lean_dec_ref_known(v___x_72_, 1);
v_flush_74_ = lean_ctor_get(v_b_69_, 0);
lean_inc_ref(v_flush_74_);
v_putStr_75_ = lean_ctor_get(v_b_69_, 4);
lean_inc_ref(v_putStr_75_);
lean_dec_ref(v_b_69_);
v___x_76_ = lean_apply_2(v_putStr_75_, v_a_73_, lean_box(0));
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_100_; 
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; 
v_unused_101_ = lean_ctor_get(v___x_76_, 0);
lean_dec(v_unused_101_);
v___x_78_ = v___x_76_;
v_isShared_79_ = v_isSharedCheck_100_;
goto v_resetjp_77_;
}
else
{
lean_dec(v___x_76_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_100_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
if (v_flushEagerly_70_ == 0)
{
lean_object* v___x_81_; 
lean_dec_ref(v_flush_74_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 0, v_a_73_);
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_a_73_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
else
{
lean_object* v___x_83_; 
lean_del_object(v___x_78_);
v___x_83_ = lean_apply_1(v_flush_74_, lean_box(0));
if (lean_obj_tag(v___x_83_) == 0)
{
lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_90_; 
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_90_ == 0)
{
lean_object* v_unused_91_; 
v_unused_91_ = lean_ctor_get(v___x_83_, 0);
lean_dec(v_unused_91_);
v___x_85_ = v___x_83_;
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
else
{
lean_dec(v___x_83_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v_a_73_);
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_a_73_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
else
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
lean_dec(v_a_73_);
v_a_92_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v___x_83_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_83_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
lean_dec_ref(v_flush_74_);
lean_dec(v_a_73_);
v_a_102_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_76_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_76_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
else
{
lean_dec_ref(v_b_69_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___lam__1___boxed(lean_object* v_getLine_110_, lean_object* v_b_111_, lean_object* v_flushEagerly_112_, lean_object* v___y_113_){
_start:
{
uint8_t v_flushEagerly_boxed_114_; lean_object* v_res_115_; 
v_flushEagerly_boxed_114_ = lean_unbox(v_flushEagerly_112_);
v_res_115_ = l_Lean_IO_FS_Stream_chainRight___lam__1(v_getLine_110_, v_b_111_, v_flushEagerly_boxed_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___lam__2(lean_object* v_flush_116_, lean_object* v_b_117_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_apply_1(v_flush_116_, lean_box(0));
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_flush_120_; lean_object* v___x_121_; 
lean_dec_ref_known(v___x_119_, 1);
v_flush_120_ = lean_ctor_get(v_b_117_, 0);
lean_inc_ref(v_flush_120_);
lean_dec_ref(v_b_117_);
v___x_121_ = lean_apply_1(v_flush_120_, lean_box(0));
return v___x_121_;
}
else
{
lean_dec_ref(v_b_117_);
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___lam__2___boxed(lean_object* v_flush_122_, lean_object* v_b_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_IO_FS_Stream_chainRight___lam__2(v_flush_122_, v_b_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight(lean_object* v_a_126_, lean_object* v_b_127_, uint8_t v_flushEagerly_128_){
_start:
{
lean_object* v_flush_129_; lean_object* v_read_130_; lean_object* v_write_131_; lean_object* v_getLine_132_; lean_object* v_putStr_133_; lean_object* v_isTty_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_146_; 
v_flush_129_ = lean_ctor_get(v_a_126_, 0);
v_read_130_ = lean_ctor_get(v_a_126_, 1);
v_write_131_ = lean_ctor_get(v_a_126_, 2);
v_getLine_132_ = lean_ctor_get(v_a_126_, 3);
v_putStr_133_ = lean_ctor_get(v_a_126_, 4);
v_isTty_134_ = lean_ctor_get(v_a_126_, 5);
v_isSharedCheck_146_ = !lean_is_exclusive(v_a_126_);
if (v_isSharedCheck_146_ == 0)
{
v___x_136_ = v_a_126_;
v_isShared_137_ = v_isSharedCheck_146_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_isTty_134_);
lean_inc(v_putStr_133_);
lean_inc(v_getLine_132_);
lean_inc(v_write_131_);
lean_inc(v_read_130_);
lean_inc(v_flush_129_);
lean_dec(v_a_126_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_146_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; lean_object* v___f_139_; lean_object* v___x_140_; lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___x_144_; 
v___x_138_ = lean_box(v_flushEagerly_128_);
lean_inc_ref_n(v_b_127_, 2);
v___f_139_ = lean_alloc_closure((void*)(l_Lean_IO_FS_Stream_chainRight___lam__0___boxed), 5, 3);
lean_closure_set(v___f_139_, 0, v_read_130_);
lean_closure_set(v___f_139_, 1, v_b_127_);
lean_closure_set(v___f_139_, 2, v___x_138_);
v___x_140_ = lean_box(v_flushEagerly_128_);
v___f_141_ = lean_alloc_closure((void*)(l_Lean_IO_FS_Stream_chainRight___lam__1___boxed), 4, 3);
lean_closure_set(v___f_141_, 0, v_getLine_132_);
lean_closure_set(v___f_141_, 1, v_b_127_);
lean_closure_set(v___f_141_, 2, v___x_140_);
v___f_142_ = lean_alloc_closure((void*)(l_Lean_IO_FS_Stream_chainRight___lam__2___boxed), 3, 2);
lean_closure_set(v___f_142_, 0, v_flush_129_);
lean_closure_set(v___f_142_, 1, v_b_127_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 3, v___f_141_);
lean_ctor_set(v___x_136_, 1, v___f_139_);
lean_ctor_set(v___x_136_, 0, v___f_142_);
v___x_144_ = v___x_136_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___f_142_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v___f_139_);
lean_ctor_set(v_reuseFailAlloc_145_, 2, v_write_131_);
lean_ctor_set(v_reuseFailAlloc_145_, 3, v___f_141_);
lean_ctor_set(v_reuseFailAlloc_145_, 4, v_putStr_133_);
lean_ctor_set(v_reuseFailAlloc_145_, 5, v_isTty_134_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___boxed(lean_object* v_a_147_, lean_object* v_b_148_, lean_object* v_flushEagerly_149_){
_start:
{
uint8_t v_flushEagerly_boxed_150_; lean_object* v_res_151_; 
v_flushEagerly_boxed_150_ = lean_unbox(v_flushEagerly_149_);
v_res_151_ = l_Lean_IO_FS_Stream_chainRight(v_a_147_, v_b_148_, v_flushEagerly_boxed_150_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__0(lean_object* v_flush_152_, lean_object* v_flush_153_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = lean_apply_1(v_flush_152_, lean_box(0));
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v___x_156_; 
lean_dec_ref_known(v___x_155_, 1);
v___x_156_ = lean_apply_1(v_flush_153_, lean_box(0));
return v___x_156_;
}
else
{
lean_dec_ref(v_flush_153_);
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__0___boxed(lean_object* v_flush_157_, lean_object* v_flush_158_, lean_object* v___y_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_IO_FS_Stream_chainLeft___lam__0(v_flush_157_, v_flush_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__1(lean_object* v_write_161_, uint8_t v_flushEagerly_162_, lean_object* v_write_163_, lean_object* v_flush_164_, lean_object* v_bs_165_){
_start:
{
lean_object* v___x_167_; 
lean_inc_ref(v_bs_165_);
v___x_167_ = lean_apply_2(v_write_161_, v_bs_165_, lean_box(0));
if (lean_obj_tag(v___x_167_) == 0)
{
lean_dec_ref_known(v___x_167_, 1);
if (v_flushEagerly_162_ == 0)
{
lean_object* v___x_168_; 
lean_dec_ref(v_flush_164_);
v___x_168_ = lean_apply_2(v_write_163_, v_bs_165_, lean_box(0));
return v___x_168_;
}
else
{
lean_object* v___x_169_; 
v___x_169_ = lean_apply_1(v_flush_164_, lean_box(0));
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v___x_170_; 
lean_dec_ref_known(v___x_169_, 1);
v___x_170_ = lean_apply_2(v_write_163_, v_bs_165_, lean_box(0));
return v___x_170_;
}
else
{
lean_dec_ref(v_bs_165_);
lean_dec_ref(v_write_163_);
return v___x_169_;
}
}
}
else
{
lean_dec_ref(v_bs_165_);
lean_dec_ref(v_flush_164_);
lean_dec_ref(v_write_163_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__1___boxed(lean_object* v_write_171_, lean_object* v_flushEagerly_172_, lean_object* v_write_173_, lean_object* v_flush_174_, lean_object* v_bs_175_, lean_object* v___y_176_){
_start:
{
uint8_t v_flushEagerly_boxed_177_; lean_object* v_res_178_; 
v_flushEagerly_boxed_177_ = lean_unbox(v_flushEagerly_172_);
v_res_178_ = l_Lean_IO_FS_Stream_chainLeft___lam__1(v_write_171_, v_flushEagerly_boxed_177_, v_write_173_, v_flush_174_, v_bs_175_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__2(lean_object* v_putStr_179_, uint8_t v_flushEagerly_180_, lean_object* v_putStr_181_, lean_object* v_flush_182_, lean_object* v_s_183_){
_start:
{
lean_object* v___x_185_; 
lean_inc_ref(v_s_183_);
v___x_185_ = lean_apply_2(v_putStr_179_, v_s_183_, lean_box(0));
if (lean_obj_tag(v___x_185_) == 0)
{
lean_dec_ref_known(v___x_185_, 1);
if (v_flushEagerly_180_ == 0)
{
lean_object* v___x_186_; 
lean_dec_ref(v_flush_182_);
v___x_186_ = lean_apply_2(v_putStr_181_, v_s_183_, lean_box(0));
return v___x_186_;
}
else
{
lean_object* v___x_187_; 
v___x_187_ = lean_apply_1(v_flush_182_, lean_box(0));
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v___x_188_; 
lean_dec_ref_known(v___x_187_, 1);
v___x_188_ = lean_apply_2(v_putStr_181_, v_s_183_, lean_box(0));
return v___x_188_;
}
else
{
lean_dec_ref(v_s_183_);
lean_dec_ref(v_putStr_181_);
return v___x_187_;
}
}
}
else
{
lean_dec_ref(v_s_183_);
lean_dec_ref(v_flush_182_);
lean_dec_ref(v_putStr_181_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__2___boxed(lean_object* v_putStr_189_, lean_object* v_flushEagerly_190_, lean_object* v_putStr_191_, lean_object* v_flush_192_, lean_object* v_s_193_, lean_object* v___y_194_){
_start:
{
uint8_t v_flushEagerly_boxed_195_; lean_object* v_res_196_; 
v_flushEagerly_boxed_195_ = lean_unbox(v_flushEagerly_190_);
v_res_196_ = l_Lean_IO_FS_Stream_chainLeft___lam__2(v_putStr_189_, v_flushEagerly_boxed_195_, v_putStr_191_, v_flush_192_, v_s_193_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft(lean_object* v_a_197_, lean_object* v_b_198_, uint8_t v_flushEagerly_199_){
_start:
{
lean_object* v_flush_200_; lean_object* v_write_201_; lean_object* v_putStr_202_; lean_object* v_flush_203_; lean_object* v_read_204_; lean_object* v_write_205_; lean_object* v_getLine_206_; lean_object* v_putStr_207_; lean_object* v_isTty_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_220_; 
v_flush_200_ = lean_ctor_get(v_a_197_, 0);
lean_inc_ref(v_flush_200_);
v_write_201_ = lean_ctor_get(v_a_197_, 2);
lean_inc_ref(v_write_201_);
v_putStr_202_ = lean_ctor_get(v_a_197_, 4);
lean_inc_ref(v_putStr_202_);
lean_dec_ref(v_a_197_);
v_flush_203_ = lean_ctor_get(v_b_198_, 0);
v_read_204_ = lean_ctor_get(v_b_198_, 1);
v_write_205_ = lean_ctor_get(v_b_198_, 2);
v_getLine_206_ = lean_ctor_get(v_b_198_, 3);
v_putStr_207_ = lean_ctor_get(v_b_198_, 4);
v_isTty_208_ = lean_ctor_get(v_b_198_, 5);
v_isSharedCheck_220_ = !lean_is_exclusive(v_b_198_);
if (v_isSharedCheck_220_ == 0)
{
v___x_210_ = v_b_198_;
v_isShared_211_ = v_isSharedCheck_220_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_isTty_208_);
lean_inc(v_putStr_207_);
lean_inc(v_getLine_206_);
lean_inc(v_write_205_);
lean_inc(v_read_204_);
lean_inc(v_flush_203_);
lean_dec(v_b_198_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_220_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___f_212_; lean_object* v___x_213_; lean_object* v___f_214_; lean_object* v___x_215_; lean_object* v___f_216_; lean_object* v___x_218_; 
lean_inc_ref_n(v_flush_200_, 2);
v___f_212_ = lean_alloc_closure((void*)(l_Lean_IO_FS_Stream_chainLeft___lam__0___boxed), 3, 2);
lean_closure_set(v___f_212_, 0, v_flush_200_);
lean_closure_set(v___f_212_, 1, v_flush_203_);
v___x_213_ = lean_box(v_flushEagerly_199_);
v___f_214_ = lean_alloc_closure((void*)(l_Lean_IO_FS_Stream_chainLeft___lam__1___boxed), 6, 4);
lean_closure_set(v___f_214_, 0, v_write_201_);
lean_closure_set(v___f_214_, 1, v___x_213_);
lean_closure_set(v___f_214_, 2, v_write_205_);
lean_closure_set(v___f_214_, 3, v_flush_200_);
v___x_215_ = lean_box(v_flushEagerly_199_);
v___f_216_ = lean_alloc_closure((void*)(l_Lean_IO_FS_Stream_chainLeft___lam__2___boxed), 6, 4);
lean_closure_set(v___f_216_, 0, v_putStr_202_);
lean_closure_set(v___f_216_, 1, v___x_215_);
lean_closure_set(v___f_216_, 2, v_putStr_207_);
lean_closure_set(v___f_216_, 3, v_flush_200_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 4, v___f_216_);
lean_ctor_set(v___x_210_, 2, v___f_214_);
lean_ctor_set(v___x_210_, 0, v___f_212_);
v___x_218_ = v___x_210_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___f_212_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_read_204_);
lean_ctor_set(v_reuseFailAlloc_219_, 2, v___f_214_);
lean_ctor_set(v_reuseFailAlloc_219_, 3, v_getLine_206_);
lean_ctor_set(v_reuseFailAlloc_219_, 4, v___f_216_);
lean_ctor_set(v_reuseFailAlloc_219_, 5, v_isTty_208_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___boxed(lean_object* v_a_221_, lean_object* v_b_222_, lean_object* v_flushEagerly_223_){
_start:
{
uint8_t v_flushEagerly_boxed_224_; lean_object* v_res_225_; 
v_flushEagerly_boxed_224_ = lean_unbox(v_flushEagerly_223_);
v_res_225_ = l_Lean_IO_FS_Stream_chainLeft(v_a_221_, v_b_222_, v_flushEagerly_boxed_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_withPrefix___lam__0(lean_object* v_putStr_226_, lean_object* v_pre_227_, lean_object* v_write_228_, lean_object* v_bs_229_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = lean_apply_2(v_putStr_226_, v_pre_227_, lean_box(0));
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v___x_232_; 
lean_dec_ref_known(v___x_231_, 1);
v___x_232_ = lean_apply_2(v_write_228_, v_bs_229_, lean_box(0));
return v___x_232_;
}
else
{
lean_dec_ref(v_bs_229_);
lean_dec_ref(v_write_228_);
return v___x_231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_withPrefix___lam__0___boxed(lean_object* v_putStr_233_, lean_object* v_pre_234_, lean_object* v_write_235_, lean_object* v_bs_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_IO_FS_Stream_withPrefix___lam__0(v_putStr_233_, v_pre_234_, v_write_235_, v_bs_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_withPrefix___lam__1(lean_object* v_pre_239_, lean_object* v_putStr_240_, lean_object* v_s_241_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_string_append(v_pre_239_, v_s_241_);
v___x_244_ = lean_apply_2(v_putStr_240_, v___x_243_, lean_box(0));
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_withPrefix___lam__1___boxed(lean_object* v_pre_245_, lean_object* v_putStr_246_, lean_object* v_s_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_IO_FS_Stream_withPrefix___lam__1(v_pre_245_, v_putStr_246_, v_s_247_);
lean_dec_ref(v_s_247_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_withPrefix(lean_object* v_a_250_, lean_object* v_pre_251_){
_start:
{
lean_object* v_flush_252_; lean_object* v_read_253_; lean_object* v_write_254_; lean_object* v_getLine_255_; lean_object* v_putStr_256_; lean_object* v_isTty_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_266_; 
v_flush_252_ = lean_ctor_get(v_a_250_, 0);
v_read_253_ = lean_ctor_get(v_a_250_, 1);
v_write_254_ = lean_ctor_get(v_a_250_, 2);
v_getLine_255_ = lean_ctor_get(v_a_250_, 3);
v_putStr_256_ = lean_ctor_get(v_a_250_, 4);
v_isTty_257_ = lean_ctor_get(v_a_250_, 5);
v_isSharedCheck_266_ = !lean_is_exclusive(v_a_250_);
if (v_isSharedCheck_266_ == 0)
{
v___x_259_ = v_a_250_;
v_isShared_260_ = v_isSharedCheck_266_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_isTty_257_);
lean_inc(v_putStr_256_);
lean_inc(v_getLine_255_);
lean_inc(v_write_254_);
lean_inc(v_read_253_);
lean_inc(v_flush_252_);
lean_dec(v_a_250_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_266_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___f_261_; lean_object* v___f_262_; lean_object* v___x_264_; 
lean_inc_ref(v_pre_251_);
lean_inc_ref(v_putStr_256_);
v___f_261_ = lean_alloc_closure((void*)(l_Lean_IO_FS_Stream_withPrefix___lam__0___boxed), 5, 3);
lean_closure_set(v___f_261_, 0, v_putStr_256_);
lean_closure_set(v___f_261_, 1, v_pre_251_);
lean_closure_set(v___f_261_, 2, v_write_254_);
v___f_262_ = lean_alloc_closure((void*)(l_Lean_IO_FS_Stream_withPrefix___lam__1___boxed), 4, 2);
lean_closure_set(v___f_262_, 0, v_pre_251_);
lean_closure_set(v___f_262_, 1, v_putStr_256_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 4, v___f_262_);
lean_ctor_set(v___x_259_, 2, v___f_261_);
v___x_264_ = v___x_259_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_flush_252_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_read_253_);
lean_ctor_set(v_reuseFailAlloc_265_, 2, v___f_261_);
lean_ctor_set(v_reuseFailAlloc_265_, 3, v_getLine_255_);
lean_ctor_set(v_reuseFailAlloc_265_, 4, v___f_262_);
lean_ctor_set(v_reuseFailAlloc_265_, 5, v_isTty_257_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
static lean_object* _init_l_Lean_Server_instInhabitedDocumentMeta_default___closed__1(void){
_start:
{
uint8_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_268_ = 0;
v___x_269_ = l_Lean_instInhabitedFileMap_default;
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = lean_box(0);
v___x_272_ = ((lean_object*)(l_Lean_Server_instInhabitedDocumentMeta_default___closed__0));
v___x_273_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v___x_271_);
lean_ctor_set(v___x_273_, 2, v___x_270_);
lean_ctor_set(v___x_273_, 3, v___x_269_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*4, v___x_268_);
return v___x_273_;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedDocumentMeta_default(void){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = lean_obj_once(&l_Lean_Server_instInhabitedDocumentMeta_default___closed__1, &l_Lean_Server_instInhabitedDocumentMeta_default___closed__1_once, _init_l_Lean_Server_instInhabitedDocumentMeta_default___closed__1);
return v___x_274_;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedDocumentMeta(void){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Server_instInhabitedDocumentMeta_default;
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DocumentMeta_mkInputContext(lean_object* v_doc_276_){
_start:
{
lean_object* v_text_277_; lean_object* v_uri_278_; lean_object* v_source_279_; lean_object* v___y_281_; lean_object* v___x_284_; 
v_text_277_ = lean_ctor_get(v_doc_276_, 3);
lean_inc_ref(v_text_277_);
v_uri_278_ = lean_ctor_get(v_doc_276_, 0);
lean_inc_ref_n(v_uri_278_, 2);
lean_dec_ref(v_doc_276_);
v_source_279_ = lean_ctor_get(v_text_277_, 0);
lean_inc_ref(v_source_279_);
v___x_284_ = l_System_Uri_fileUriToPath_x3f(v_uri_278_);
if (lean_obj_tag(v___x_284_) == 0)
{
v___y_281_ = v_uri_278_;
goto v___jp_280_;
}
else
{
lean_object* v_val_285_; 
lean_dec_ref(v_uri_278_);
v_val_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_val_285_);
lean_dec_ref_known(v___x_284_, 1);
v___y_281_ = v_val_285_;
goto v___jp_280_;
}
v___jp_280_:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_string_utf8_byte_size(v_source_279_);
v___x_283_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_283_, 0, v_source_279_);
lean_ctor_set(v___x_283_, 1, v___y_281_);
lean_ctor_set(v___x_283_, 2, v_text_277_);
lean_ctor_set(v___x_283_, 3, v___x_282_);
return v___x_283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_replaceLspRange(lean_object* v_text_286_, lean_object* v_r_287_, lean_object* v_newText_288_){
_start:
{
lean_object* v_start_289_; lean_object* v_end_290_; lean_object* v_source_291_; lean_object* v_start_292_; lean_object* v_end_293_; lean_object* v___x_294_; lean_object* v_pre_295_; lean_object* v___x_296_; lean_object* v_post_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v_start_289_ = lean_ctor_get(v_r_287_, 0);
lean_inc_ref(v_start_289_);
v_end_290_ = lean_ctor_get(v_r_287_, 1);
lean_inc_ref(v_end_290_);
lean_dec_ref(v_r_287_);
v_source_291_ = lean_ctor_get(v_text_286_, 0);
v_start_292_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_286_, v_start_289_);
v_end_293_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_286_, v_end_290_);
v___x_294_ = lean_unsigned_to_nat(0u);
v_pre_295_ = lean_string_utf8_extract(v_source_291_, v___x_294_, v_start_292_);
lean_dec(v_start_292_);
v___x_296_ = lean_string_utf8_byte_size(v_source_291_);
v_post_297_ = lean_string_utf8_extract(v_source_291_, v_end_293_, v___x_296_);
lean_dec(v_end_293_);
v___x_298_ = l_String_crlfToLf(v_newText_288_);
v___x_299_ = lean_string_append(v_pre_295_, v___x_298_);
lean_dec_ref(v___x_298_);
v___x_300_ = lean_string_append(v___x_299_, v_post_297_);
lean_dec_ref(v_post_297_);
v___x_301_ = l_Lean_String_toFileMap(v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_replaceLspRange___boxed(lean_object* v_text_302_, lean_object* v_r_303_, lean_object* v_newText_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Server_replaceLspRange(v_text_302_, v_r_303_, v_newText_304_);
lean_dec_ref(v_newText_304_);
lean_dec_ref(v_text_302_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_applyDocumentChange(lean_object* v_oldText_306_, lean_object* v_x_307_){
_start:
{
if (lean_obj_tag(v_x_307_) == 0)
{
lean_object* v_range_308_; lean_object* v_text_309_; lean_object* v___x_310_; 
v_range_308_ = lean_ctor_get(v_x_307_, 0);
lean_inc_ref(v_range_308_);
v_text_309_ = lean_ctor_get(v_x_307_, 1);
lean_inc_ref(v_text_309_);
lean_dec_ref_known(v_x_307_, 2);
v___x_310_ = l_Lean_Server_replaceLspRange(v_oldText_306_, v_range_308_, v_text_309_);
lean_dec_ref(v_text_309_);
return v___x_310_;
}
else
{
lean_object* v_text_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_text_311_ = lean_ctor_get(v_x_307_, 0);
lean_inc_ref(v_text_311_);
lean_dec_ref_known(v_x_307_, 1);
v___x_312_ = l_String_crlfToLf(v_text_311_);
lean_dec_ref(v_text_311_);
v___x_313_ = l_Lean_String_toFileMap(v___x_312_);
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_applyDocumentChange___boxed(lean_object* v_oldText_314_, lean_object* v_x_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_Server_applyDocumentChange(v_oldText_314_, v_x_315_);
lean_dec_ref(v_oldText_314_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(lean_object* v_as_317_, size_t v_i_318_, size_t v_stop_319_, lean_object* v_b_320_){
_start:
{
uint8_t v___x_321_; 
v___x_321_ = lean_usize_dec_eq(v_i_318_, v_stop_319_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; size_t v___x_324_; size_t v___x_325_; 
v___x_322_ = lean_array_uget_borrowed(v_as_317_, v_i_318_);
lean_inc(v___x_322_);
v___x_323_ = l_Lean_Server_applyDocumentChange(v_b_320_, v___x_322_);
lean_dec_ref(v_b_320_);
v___x_324_ = ((size_t)1ULL);
v___x_325_ = lean_usize_add(v_i_318_, v___x_324_);
v_i_318_ = v___x_325_;
v_b_320_ = v___x_323_;
goto _start;
}
else
{
return v_b_320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0___boxed(lean_object* v_as_327_, lean_object* v_i_328_, lean_object* v_stop_329_, lean_object* v_b_330_){
_start:
{
size_t v_i_boxed_331_; size_t v_stop_boxed_332_; lean_object* v_res_333_; 
v_i_boxed_331_ = lean_unbox_usize(v_i_328_);
lean_dec(v_i_328_);
v_stop_boxed_332_ = lean_unbox_usize(v_stop_329_);
lean_dec(v_stop_329_);
v_res_333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(v_as_327_, v_i_boxed_331_, v_stop_boxed_332_, v_b_330_);
lean_dec_ref(v_as_327_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_foldDocumentChanges(lean_object* v_changes_334_, lean_object* v_oldText_335_){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_336_ = lean_unsigned_to_nat(0u);
v___x_337_ = lean_array_get_size(v_changes_334_);
v___x_338_ = lean_nat_dec_lt(v___x_336_, v___x_337_);
if (v___x_338_ == 0)
{
return v_oldText_335_;
}
else
{
size_t v___x_339_; size_t v___x_340_; lean_object* v___x_341_; 
v___x_339_ = ((size_t)0ULL);
v___x_340_ = lean_usize_of_nat(v___x_337_);
v___x_341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(v_changes_334_, v___x_339_, v___x_340_, v_oldText_335_);
return v___x_341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_foldDocumentChanges___boxed(lean_object* v_changes_342_, lean_object* v_oldText_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Server_foldDocumentChanges(v_changes_342_, v_oldText_343_);
lean_dec_ref(v_changes_342_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Server_mkPublishDiagnosticsNotification_spec__0(lean_object* v_a_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = lean_nat_to_int(v_a_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_mkPublishDiagnosticsNotification(lean_object* v_m_348_, lean_object* v_diagnostics_349_, lean_object* v_isIncremental_350_){
_start:
{
lean_object* v_uri_351_; lean_object* v_version_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_uri_351_ = lean_ctor_get(v_m_348_, 0);
lean_inc_ref(v_uri_351_);
v_version_352_ = lean_ctor_get(v_m_348_, 2);
lean_inc(v_version_352_);
lean_dec_ref(v_m_348_);
v___x_353_ = ((lean_object*)(l_Lean_Server_mkPublishDiagnosticsNotification___closed__0));
v___x_354_ = lean_nat_to_int(v_version_352_);
v___x_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
v___x_356_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_356_, 0, v_uri_351_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
lean_ctor_set(v___x_356_, 2, v_isIncremental_350_);
lean_ctor_set(v___x_356_, 3, v_diagnostics_349_);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_353_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressNotification(lean_object* v_m_359_, lean_object* v_processing_360_){
_start:
{
lean_object* v_uri_361_; lean_object* v_version_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_uri_361_ = lean_ctor_get(v_m_359_, 0);
v_version_362_ = lean_ctor_get(v_m_359_, 2);
v___x_363_ = ((lean_object*)(l_Lean_Server_mkFileProgressNotification___closed__0));
lean_inc(v_version_362_);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v_version_362_);
lean_inc_ref(v_uri_361_);
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v_uri_361_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v_processing_360_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_363_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressNotification___boxed(lean_object* v_m_368_, lean_object* v_processing_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Server_mkFileProgressNotification(v_m_368_, v_processing_369_);
lean_dec_ref(v_m_368_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressAtPosNotification(lean_object* v_m_371_, lean_object* v_pos_372_, uint8_t v_kind_373_){
_start:
{
lean_object* v_text_374_; lean_object* v_source_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v_text_374_ = lean_ctor_get(v_m_371_, 3);
v_source_375_ = lean_ctor_get(v_text_374_, 0);
lean_inc_ref_n(v_text_374_, 2);
v___x_376_ = l_Lean_FileMap_utf8PosToLspPos(v_text_374_, v_pos_372_);
v___x_377_ = lean_string_utf8_byte_size(v_source_375_);
v___x_378_ = l_Lean_FileMap_utf8PosToLspPos(v_text_374_, v___x_377_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_376_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set_uint8(v___x_380_, sizeof(void*)*1, v_kind_373_);
v___x_381_ = lean_unsigned_to_nat(1u);
v___x_382_ = lean_mk_empty_array_with_capacity(v___x_381_);
v___x_383_ = lean_array_push(v___x_382_, v___x_380_);
v___x_384_ = l_Lean_Server_mkFileProgressNotification(v_m_371_, v___x_383_);
lean_dec_ref(v_m_371_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressAtPosNotification___boxed(lean_object* v_m_385_, lean_object* v_pos_386_, lean_object* v_kind_387_){
_start:
{
uint8_t v_kind_boxed_388_; lean_object* v_res_389_; 
v_kind_boxed_388_ = lean_unbox(v_kind_387_);
v_res_389_ = l_Lean_Server_mkFileProgressAtPosNotification(v_m_385_, v_pos_386_, v_kind_boxed_388_);
lean_dec(v_pos_386_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressDoneNotification(lean_object* v_m_392_){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = ((lean_object*)(l_Lean_Server_mkFileProgressDoneNotification___closed__0));
v___x_394_ = l_Lean_Server_mkFileProgressNotification(v_m_392_, v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressDoneNotification___boxed(lean_object* v_m_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Server_mkFileProgressDoneNotification(v_m_395_);
lean_dec_ref(v_m_395_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_mkApplyWorkspaceEditRequest(lean_object* v_params_400_){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_401_ = ((lean_object*)(l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0));
v___x_402_ = ((lean_object*)(l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1));
v___x_403_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v___x_401_);
lean_ctor_set(v___x_403_, 2, v_params_400_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(lean_object* v_uri_405_){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_406_ = lean_box(0);
v___x_407_ = ((lean_object*)(l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0));
v___x_408_ = lean_string_append(v___x_407_, v_uri_405_);
v___x_409_ = l_Lean_Name_str___override(v___x_406_, v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___boxed(lean_object* v_uri_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(v_uri_410_);
lean_dec_ref(v_uri_410_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg(lean_object* v_s_412_){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_413_ = lean_string_utf8_byte_size(v_s_412_);
v___x_414_ = lean_unsigned_to_nat(9u);
v___x_415_ = lean_nat_dec_le(v___x_414_, v___x_413_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; 
lean_dec_ref(v_s_412_);
v___x_416_ = lean_box(0);
return v___x_416_;
}
else
{
lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_417_ = ((lean_object*)(l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0));
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = lean_string_memcmp(v_s_412_, v___x_417_, v___x_418_, v___x_418_, v___x_414_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; 
lean_dec_ref(v_s_412_);
v___x_420_ = lean_box(0);
return v___x_420_;
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
lean_inc_ref(v_s_412_);
v___x_421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_421_, 0, v_s_412_);
lean_ctor_set(v___x_421_, 1, v___x_418_);
lean_ctor_set(v___x_421_, 2, v___x_413_);
v___x_422_ = l_String_Slice_pos_x21(v___x_421_, v___x_414_);
lean_dec_ref_known(v___x_421_, 3);
v___x_423_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_423_, 0, v_s_412_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
lean_ctor_set(v___x_423_, 2, v___x_413_);
v___x_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0(lean_object* v_s_425_, lean_object* v_pat_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg(v_s_425_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___boxed(lean_object* v_s_428_, lean_object* v_pat_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0(v_s_428_, v_pat_429_);
lean_dec_ref(v_pat_429_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f(lean_object* v_name_431_){
_start:
{
if (lean_obj_tag(v_name_431_) == 1)
{
lean_object* v_pre_432_; 
v_pre_432_ = lean_ctor_get(v_name_431_, 0);
if (lean_obj_tag(v_pre_432_) == 0)
{
lean_object* v_str_433_; lean_object* v___x_434_; 
v_str_433_ = lean_ctor_get(v_name_431_, 1);
lean_inc_ref(v_str_433_);
lean_dec_ref_known(v_name_431_, 2);
v___x_434_ = l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg(v_str_433_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v___x_435_; 
v___x_435_ = lean_box(0);
return v___x_435_;
}
else
{
lean_object* v_val_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_444_; 
v_val_436_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_444_ == 0)
{
v___x_438_ = v___x_434_;
v_isShared_439_ = v_isSharedCheck_444_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_val_436_);
lean_dec(v___x_434_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_444_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_440_ = l_String_Slice_toString(v_val_436_);
lean_dec(v_val_436_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_440_);
v___x_442_ = v___x_438_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
else
{
lean_object* v___x_445_; 
lean_dec_ref_known(v_name_431_, 2);
v___x_445_ = lean_box(0);
return v___x_445_;
}
}
else
{
lean_object* v___x_446_; 
lean_dec(v_name_431_);
v___x_446_ = lean_box(0);
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_documentUriFromModule_x3f(lean_object* v_modName_448_){
_start:
{
lean_object* v___x_450_; 
lean_inc(v_modName_448_);
v___x_450_ = l___private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f(v_modName_448_);
if (lean_obj_tag(v___x_450_) == 1)
{
lean_object* v___x_451_; 
lean_dec(v_modName_448_);
v___x_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
return v___x_451_;
}
else
{
lean_object* v___x_452_; 
lean_dec(v___x_450_);
v___x_452_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_a_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v_a_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_a_453_);
lean_dec_ref_known(v___x_452_, 1);
v___x_454_ = ((lean_object*)(l_Lean_Server_documentUriFromModule_x3f___closed__0));
v___x_455_ = l_Lean_SearchPath_findModuleWithExt(v_a_453_, v___x_454_, v_modName_448_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_490_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_490_ == 0)
{
v___x_458_ = v___x_455_;
v_isShared_459_ = v_isSharedCheck_490_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_490_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
if (lean_obj_tag(v_a_456_) == 1)
{
lean_object* v_val_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_485_; 
lean_del_object(v___x_458_);
v_val_460_ = lean_ctor_get(v_a_456_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v_a_456_);
if (v_isSharedCheck_485_ == 0)
{
v___x_462_ = v_a_456_;
v_isShared_463_ = v_isSharedCheck_485_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_val_460_);
lean_dec(v_a_456_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_485_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; 
v___x_464_ = lean_io_realpath(v_val_460_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_476_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_476_ == 0)
{
v___x_467_ = v___x_464_;
v_isShared_468_ = v_isSharedCheck_476_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_476_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_469_ = l_System_Uri_pathToUri(v_a_465_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___x_469_);
v___x_471_ = v___x_462_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_469_);
v___x_471_ = v_reuseFailAlloc_475_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_473_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v___x_471_);
v___x_473_ = v___x_467_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
lean_del_object(v___x_462_);
v_a_477_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_464_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_464_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
}
else
{
lean_object* v___x_486_; lean_object* v___x_488_; 
lean_dec(v_a_456_);
v___x_486_ = lean_box(0);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_486_);
v___x_488_ = v___x_458_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
v_a_491_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_455_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_455_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_dec(v_modName_448_);
v_a_499_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_452_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_452_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_documentUriFromModule_x3f___boxed(lean_object* v_modName_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Server_documentUriFromModule_x3f(v_modName_507_);
return v_res_509_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0(lean_object* v_x_510_, lean_object* v_x_511_){
_start:
{
if (lean_obj_tag(v_x_510_) == 0)
{
if (lean_obj_tag(v_x_511_) == 0)
{
uint8_t v___x_512_; 
v___x_512_ = 1;
return v___x_512_;
}
else
{
uint8_t v___x_513_; 
v___x_513_ = 0;
return v___x_513_;
}
}
else
{
if (lean_obj_tag(v_x_511_) == 0)
{
uint8_t v___x_514_; 
v___x_514_ = 0;
return v___x_514_;
}
else
{
lean_object* v_val_515_; lean_object* v_val_516_; uint8_t v___x_517_; 
v_val_515_ = lean_ctor_get(v_x_510_, 0);
v_val_516_ = lean_ctor_get(v_x_511_, 0);
v___x_517_ = lean_string_dec_eq(v_val_515_, v_val_516_);
return v___x_517_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0___boxed(lean_object* v_x_518_, lean_object* v_x_519_){
_start:
{
uint8_t v_res_520_; lean_object* v_r_521_; 
v_res_520_ = l_instBEqOption_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0(v_x_518_, v_x_519_);
lean_dec(v_x_519_);
lean_dec(v_x_518_);
v_r_521_ = lean_box(v_res_520_);
return v_r_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_moduleFromDocumentUri(lean_object* v_uri_524_){
_start:
{
lean_object* v___x_526_; 
lean_inc_ref(v_uri_524_);
v___x_526_ = l_System_Uri_fileUriToPath_x3f(v_uri_524_);
if (lean_obj_tag(v___x_526_) == 1)
{
lean_object* v_val_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_570_; 
v_val_527_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_570_ == 0)
{
v___x_529_ = v___x_526_;
v_isShared_530_ = v_isSharedCheck_570_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_val_527_);
lean_dec(v___x_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_570_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
lean_inc(v_val_527_);
v___x_531_ = l_System_FilePath_extension(v_val_527_);
v___x_532_ = ((lean_object*)(l_Lean_Server_moduleFromDocumentUri___closed__0));
v___x_533_ = l_instBEqOption_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0(v___x_531_, v___x_532_);
lean_dec(v___x_531_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_536_; 
lean_dec(v_val_527_);
v___x_534_ = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(v_uri_524_);
lean_dec_ref(v_uri_524_);
if (v_isShared_530_ == 0)
{
lean_ctor_set_tag(v___x_529_, 0);
lean_ctor_set(v___x_529_, 0, v___x_534_);
v___x_536_ = v___x_529_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
else
{
lean_object* v___x_538_; 
lean_del_object(v___x_529_);
v___x_538_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_540_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_539_);
lean_dec_ref_known(v___x_538_, 1);
v___x_540_ = l_Lean_searchModuleNameOfFileName(v_val_527_, v_a_539_);
lean_dec(v_a_539_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_553_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_553_ == 0)
{
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_553_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_553_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
if (lean_obj_tag(v_a_541_) == 1)
{
lean_object* v_val_545_; lean_object* v___x_547_; 
lean_dec_ref(v_uri_524_);
v_val_545_ = lean_ctor_get(v_a_541_, 0);
lean_inc(v_val_545_);
lean_dec_ref_known(v_a_541_, 1);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v_val_545_);
v___x_547_ = v___x_543_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_val_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
else
{
lean_object* v___x_549_; lean_object* v___x_551_; 
lean_dec(v_a_541_);
v___x_549_ = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(v_uri_524_);
lean_dec_ref(v_uri_524_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_549_);
v___x_551_ = v___x_543_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec_ref(v_uri_524_);
v_a_554_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_540_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_540_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_dec(v_val_527_);
lean_dec_ref(v_uri_524_);
v_a_562_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_538_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_538_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec(v___x_526_);
v___x_571_ = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(v_uri_524_);
lean_dec_ref(v_uri_524_);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_moduleFromDocumentUri___boxed(lean_object* v_uri_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Server_moduleFromDocumentUri(v_uri_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_toLspRange(lean_object* v_text_576_, lean_object* v_r_577_){
_start:
{
lean_object* v_start_578_; lean_object* v_stop_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_588_; 
v_start_578_ = lean_ctor_get(v_r_577_, 0);
v_stop_579_ = lean_ctor_get(v_r_577_, 1);
v_isSharedCheck_588_ = !lean_is_exclusive(v_r_577_);
if (v_isSharedCheck_588_ == 0)
{
v___x_581_ = v_r_577_;
v_isShared_582_ = v_isSharedCheck_588_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_stop_579_);
lean_inc(v_start_578_);
lean_dec(v_r_577_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_588_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
lean_inc_ref(v_text_576_);
v___x_583_ = l_Lean_FileMap_utf8PosToLspPos(v_text_576_, v_start_578_);
lean_dec(v_start_578_);
v___x_584_ = l_Lean_FileMap_utf8PosToLspPos(v_text_576_, v_stop_579_);
lean_dec(v_stop_579_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v___x_584_);
lean_ctor_set(v___x_581_, 0, v___x_583_);
v___x_586_ = v___x_581_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
lean_object* runtime_initialize_Init_System_Uri(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_Communication(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_Diagnostics(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_Extra(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Utils(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_System_Uri(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Communication(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Diagnostics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_InfoTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_instInhabitedDocumentMeta_default = _init_l_Lean_Server_instInhabitedDocumentMeta_default();
lean_mark_persistent(l_Lean_Server_instInhabitedDocumentMeta_default);
l_Lean_Server_instInhabitedDocumentMeta = _init_l_Lean_Server_instInhabitedDocumentMeta();
lean_mark_persistent(l_Lean_Server_instInhabitedDocumentMeta);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_Utils(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_Uri(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_Communication(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_Diagnostics(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_Extra(uint8_t builtin);
lean_object* initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Utils(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_Uri(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Communication(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Diagnostics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Utils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_Utils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_Utils(builtin);
}
#ifdef __cplusplus
}
#endif
