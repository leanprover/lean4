// Lean compiler output
// Module: Std.Time.Zoned.Database.TZdb
// Imports: public import Std.Time.Zoned.Database.Basic import Init.Data.String.TakeDrop
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
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_realpath(lean_object*);
lean_object* l_System_FilePath_components(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*);
lean_object* l_Std_Time_TimeZone_TZif_parse(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_convertTZif(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* lean_io_getenv(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_Database_TZdb_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "/etc/localtime"};
static const lean_object* l_Std_Time_Database_TZdb_default___closed__0 = (const lean_object*)&l_Std_Time_Database_TZdb_default___closed__0_value;
static const lean_string_object l_Std_Time_Database_TZdb_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "/usr/share/zoneinfo"};
static const lean_object* l_Std_Time_Database_TZdb_default___closed__1 = (const lean_object*)&l_Std_Time_Database_TZdb_default___closed__1_value;
static const lean_string_object l_Std_Time_Database_TZdb_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "/share/zoneinfo"};
static const lean_object* l_Std_Time_Database_TZdb_default___closed__2 = (const lean_object*)&l_Std_Time_Database_TZdb_default___closed__2_value;
static const lean_string_object l_Std_Time_Database_TZdb_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "/etc/zoneinfo"};
static const lean_object* l_Std_Time_Database_TZdb_default___closed__3 = (const lean_object*)&l_Std_Time_Database_TZdb_default___closed__3_value;
static const lean_string_object l_Std_Time_Database_TZdb_default___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "/usr/share/lib/zoneinfo"};
static const lean_object* l_Std_Time_Database_TZdb_default___closed__4 = (const lean_object*)&l_Std_Time_Database_TZdb_default___closed__4_value;
static const lean_array_object l_Std_Time_Database_TZdb_default___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_Std_Time_Database_TZdb_default___closed__1_value),((lean_object*)&l_Std_Time_Database_TZdb_default___closed__2_value),((lean_object*)&l_Std_Time_Database_TZdb_default___closed__3_value),((lean_object*)&l_Std_Time_Database_TZdb_default___closed__4_value)}};
static const lean_object* l_Std_Time_Database_TZdb_default___closed__5 = (const lean_object*)&l_Std_Time_Database_TZdb_default___closed__5_value;
static const lean_ctor_object l_Std_Time_Database_TZdb_default___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Database_TZdb_default___closed__0_value),((lean_object*)&l_Std_Time_Database_TZdb_default___closed__5_value)}};
static const lean_object* l_Std_Time_Database_TZdb_default___closed__6 = (const lean_object*)&l_Std_Time_Database_TZdb_default___closed__6_value;
LEAN_EXPORT const lean_object* l_Std_Time_Database_TZdb_default = (const lean_object*)&l_Std_Time_Database_TZdb_default___closed__6_value;
static const lean_closure_object l_Std_Time_Database_TZdb_parseTZif___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_TZif_parse, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Database_TZdb_parseTZif___closed__0 = (const lean_object*)&l_Std_Time_Database_TZdb_parseTZif___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZif(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "unable to locate "};
static const lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__0 = (const lean_object*)&l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__0_value;
static const lean_string_object l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = " in the local timezone database at '"};
static const lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__1 = (const lean_object*)&l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__1_value;
static const lean_string_object l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__2 = (const lean_object*)&l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_Database_TZdb_idFromPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "zoneinfo"};
static const lean_object* l_Std_Time_Database_TZdb_idFromPath___closed__0 = (const lean_object*)&l_Std_Time_Database_TZdb_idFromPath___closed__0_value;
static const lean_string_object l_Std_Time_Database_TZdb_idFromPath___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Std_Time_Database_TZdb_idFromPath___closed__1 = (const lean_object*)&l_Std_Time_Database_TZdb_idFromPath___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_idFromPath(lean_object*);
static const lean_string_object l_Std_Time_Database_TZdb_localRules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "cannot read the id of the path."};
static const lean_object* l_Std_Time_Database_TZdb_localRules___closed__0 = (const lean_object*)&l_Std_Time_Database_TZdb_localRules___closed__0_value;
static lean_once_cell_t l_Std_Time_Database_TZdb_localRules___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Database_TZdb_localRules___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_localRules(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_localRules___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_readRulesFromDisk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_readRulesFromDisk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_inst___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_inst___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_inst___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_inst___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_Database_TZdb_inst___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "TZDIR"};
static const lean_object* l_Std_Time_Database_TZdb_inst___lam__2___closed__0 = (const lean_object*)&l_Std_Time_Database_TZdb_inst___lam__2___closed__0_value;
static const lean_ctor_object l_Std_Time_Database_TZdb_inst___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Database_TZdb_inst___lam__2___closed__1 = (const lean_object*)&l_Std_Time_Database_TZdb_inst___lam__2___closed__1_value;
static const lean_string_object l_Std_Time_Database_TZdb_inst___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "cannot find "};
static const lean_object* l_Std_Time_Database_TZdb_inst___lam__2___closed__2 = (const lean_object*)&l_Std_Time_Database_TZdb_inst___lam__2___closed__2_value;
static const lean_string_object l_Std_Time_Database_TZdb_inst___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = " in the local timezone database"};
static const lean_object* l_Std_Time_Database_TZdb_inst___lam__2___closed__3 = (const lean_object*)&l_Std_Time_Database_TZdb_inst___lam__2___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_inst___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_inst___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Database_TZdb_inst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Database_TZdb_inst___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Database_TZdb_inst___closed__0 = (const lean_object*)&l_Std_Time_Database_TZdb_inst___closed__0_value;
static lean_once_cell_t l_Std_Time_Database_TZdb_inst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Database_TZdb_inst___closed__1;
static lean_once_cell_t l_Std_Time_Database_TZdb_inst___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Database_TZdb_inst___closed__2;
static lean_once_cell_t l_Std_Time_Database_TZdb_inst___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Database_TZdb_inst___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_inst;
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZif(lean_object* v_bin_21_, lean_object* v_id_22_){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = ((lean_object*)(l_Std_Time_Database_TZdb_parseTZif___closed__0));
v___x_24_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_23_, v_bin_21_);
if (lean_obj_tag(v___x_24_) == 0)
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_dec_ref(v_id_22_);
v_a_25_ = lean_ctor_get(v___x_24_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_24_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_24_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
else
{
lean_object* v_a_33_; lean_object* v___x_34_; 
v_a_33_ = lean_ctor_get(v___x_24_, 0);
lean_inc(v_a_33_);
lean_dec_ref(v___x_24_);
v___x_34_ = l_Std_Time_TimeZone_convertTZif(v_a_33_, v_id_22_);
lean_dec(v_a_33_);
return v___x_34_;
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg(lean_object* v_e_35_){
_start:
{
if (lean_obj_tag(v_e_35_) == 0)
{
lean_object* v_a_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_45_; 
v_a_37_ = lean_ctor_get(v_e_35_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v_e_35_);
if (v_isSharedCheck_45_ == 0)
{
v___x_39_ = v_e_35_;
v_isShared_40_ = v_isSharedCheck_45_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_a_37_);
lean_dec(v_e_35_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_45_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_41_; lean_object* v___x_43_; 
v___x_41_ = lean_mk_io_user_error(v_a_37_);
if (v_isShared_40_ == 0)
{
lean_ctor_set_tag(v___x_39_, 1);
lean_ctor_set(v___x_39_, 0, v___x_41_);
v___x_43_ = v___x_39_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_41_);
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
v_a_46_ = lean_ctor_get(v_e_35_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v_e_35_);
if (v_isSharedCheck_53_ == 0)
{
v___x_48_ = v_e_35_;
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v_e_35_);
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
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg___boxed(lean_object* v_e_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg(v_e_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0(lean_object* v_00_u03b1_57_, lean_object* v_e_58_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg(v_e_58_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___boxed(lean_object* v_00_u03b1_61_, lean_object* v_e_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0(v_00_u03b1_61_, v_e_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk(lean_object* v_path_68_, lean_object* v_id_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_IO_FS_readBinFile(v_path_68_);
if (lean_obj_tag(v___x_71_) == 0)
{
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v_a_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v_a_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc(v_a_72_);
lean_dec_ref(v___x_71_);
v___x_73_ = l_Std_Time_Database_TZdb_parseTZif(v_a_72_, v_id_69_);
v___x_74_ = l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg(v___x_73_);
return v___x_74_;
}
else
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
lean_dec_ref(v_id_69_);
v_a_75_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v___x_71_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_71_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
lean_ctor_set_tag(v___x_77_, 1);
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_a_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
else
{
lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_97_; 
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_97_ == 0)
{
lean_object* v_unused_98_; 
v_unused_98_ = lean_ctor_get(v___x_71_, 0);
lean_dec(v_unused_98_);
v___x_84_ = v___x_71_;
v_isShared_85_ = v_isSharedCheck_97_;
goto v_resetjp_83_;
}
else
{
lean_dec(v___x_71_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_97_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_86_ = ((lean_object*)(l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__0));
v___x_87_ = lean_string_append(v___x_86_, v_id_69_);
lean_dec_ref(v_id_69_);
v___x_88_ = ((lean_object*)(l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__1));
v___x_89_ = lean_string_append(v___x_87_, v___x_88_);
v___x_90_ = lean_string_append(v___x_89_, v_path_68_);
v___x_91_ = ((lean_object*)(l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__2));
v___x_92_ = lean_string_append(v___x_90_, v___x_91_);
v___x_93_ = lean_mk_io_user_error(v___x_92_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 0, v___x_93_);
v___x_95_ = v___x_84_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_parseTZIfFromDisk___boxed(lean_object* v_path_99_, lean_object* v_id_100_, lean_object* v_a_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Std_Time_Database_TZdb_parseTZIfFromDisk(v_path_99_, v_id_100_);
lean_dec_ref(v_path_99_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_idFromPath(lean_object* v_path_105_){
_start:
{
lean_object* v___x_106_; lean_object* v_res_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_106_ = l_System_FilePath_components(v_path_105_);
v_res_107_ = lean_array_mk(v___x_106_);
v___x_108_ = lean_array_get_size(v_res_107_);
v___x_109_ = lean_unsigned_to_nat(1u);
v___x_110_ = lean_nat_sub(v___x_108_, v___x_109_);
v___x_111_ = lean_nat_dec_lt(v___x_110_, v___x_108_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; 
lean_dec(v___x_110_);
lean_dec_ref(v_res_107_);
v___x_112_ = lean_box(0);
return v___x_112_;
}
else
{
lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_113_ = lean_unsigned_to_nat(2u);
v___x_114_ = lean_nat_sub(v___x_108_, v___x_113_);
v___x_115_ = lean_nat_dec_lt(v___x_114_, v___x_108_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; 
lean_dec(v___x_114_);
lean_dec(v___x_110_);
lean_dec_ref(v_res_107_);
v___x_116_ = lean_box(0);
return v___x_116_;
}
else
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_117_ = lean_array_fget(v_res_107_, v___x_110_);
lean_dec(v___x_110_);
v___x_118_ = lean_array_fget(v_res_107_, v___x_114_);
lean_dec(v___x_114_);
lean_dec_ref(v_res_107_);
v___x_119_ = ((lean_object*)(l_Std_Time_Database_TZdb_idFromPath___closed__0));
v___x_120_ = lean_string_dec_eq(v___x_118_, v___x_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_str_125_; lean_object* v_startInclusive_126_; lean_object* v_endExclusive_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_145_; 
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_string_utf8_byte_size(v___x_118_);
v___x_123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_123_, 0, v___x_118_);
lean_ctor_set(v___x_123_, 1, v___x_121_);
lean_ctor_set(v___x_123_, 2, v___x_122_);
v___x_124_ = l_String_Slice_trimAscii(v___x_123_);
v_str_125_ = lean_ctor_get(v___x_124_, 0);
v_startInclusive_126_ = lean_ctor_get(v___x_124_, 1);
v_endExclusive_127_ = lean_ctor_get(v___x_124_, 2);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_145_ == 0)
{
v___x_129_ = v___x_124_;
v_isShared_130_ = v_isSharedCheck_145_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_endExclusive_127_);
lean_inc(v_startInclusive_126_);
lean_inc(v_str_125_);
lean_dec(v___x_124_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_145_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_131_ = lean_string_utf8_byte_size(v___x_117_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 2, v___x_131_);
lean_ctor_set(v___x_129_, 1, v___x_121_);
lean_ctor_set(v___x_129_, 0, v___x_117_);
v___x_133_ = v___x_129_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_117_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_144_, 2, v___x_131_);
v___x_133_ = v_reuseFailAlloc_144_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_134_; lean_object* v_str_135_; lean_object* v_startInclusive_136_; lean_object* v_endExclusive_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_134_ = l_String_Slice_trimAscii(v___x_133_);
v_str_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc_ref(v_str_135_);
v_startInclusive_136_ = lean_ctor_get(v___x_134_, 1);
lean_inc(v_startInclusive_136_);
v_endExclusive_137_ = lean_ctor_get(v___x_134_, 2);
lean_inc(v_endExclusive_137_);
lean_dec_ref(v___x_134_);
v___x_138_ = lean_string_utf8_extract(v_str_125_, v_startInclusive_126_, v_endExclusive_127_);
lean_dec(v_endExclusive_127_);
lean_dec(v_startInclusive_126_);
lean_dec_ref(v_str_125_);
v___x_139_ = ((lean_object*)(l_Std_Time_Database_TZdb_idFromPath___closed__1));
v___x_140_ = lean_string_append(v___x_138_, v___x_139_);
v___x_141_ = lean_string_utf8_extract(v_str_135_, v_startInclusive_136_, v_endExclusive_137_);
lean_dec(v_endExclusive_137_);
lean_dec(v_startInclusive_136_);
lean_dec_ref(v_str_135_);
v___x_142_ = lean_string_append(v___x_140_, v___x_141_);
lean_dec_ref(v___x_141_);
v___x_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
return v___x_143_;
}
}
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v_str_150_; lean_object* v_startInclusive_151_; lean_object* v_endExclusive_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec(v___x_118_);
v___x_146_ = lean_unsigned_to_nat(0u);
v___x_147_ = lean_string_utf8_byte_size(v___x_117_);
v___x_148_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_148_, 0, v___x_117_);
lean_ctor_set(v___x_148_, 1, v___x_146_);
lean_ctor_set(v___x_148_, 2, v___x_147_);
v___x_149_ = l_String_Slice_trimAscii(v___x_148_);
v_str_150_ = lean_ctor_get(v___x_149_, 0);
lean_inc_ref(v_str_150_);
v_startInclusive_151_ = lean_ctor_get(v___x_149_, 1);
lean_inc(v_startInclusive_151_);
v_endExclusive_152_ = lean_ctor_get(v___x_149_, 2);
lean_inc(v_endExclusive_152_);
lean_dec_ref(v___x_149_);
v___x_153_ = lean_string_utf8_extract(v_str_150_, v_startInclusive_151_, v_endExclusive_152_);
lean_dec(v_endExclusive_152_);
lean_dec(v_startInclusive_151_);
lean_dec_ref(v_str_150_);
v___x_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
}
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_localRules___closed__1(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = ((lean_object*)(l_Std_Time_Database_TZdb_localRules___closed__0));
v___x_157_ = lean_mk_io_user_error(v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_localRules(lean_object* v_path_158_){
_start:
{
lean_object* v___x_160_; 
lean_inc_ref(v_path_158_);
v___x_160_ = lean_io_realpath(v_path_158_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_172_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_172_ == 0)
{
v___x_163_ = v___x_160_;
v_isShared_164_ = v_isSharedCheck_172_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_172_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_165_; 
v___x_165_ = l_Std_Time_Database_TZdb_idFromPath(v_a_161_);
if (lean_obj_tag(v___x_165_) == 1)
{
lean_object* v_val_166_; lean_object* v___x_167_; 
lean_del_object(v___x_163_);
v_val_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_val_166_);
lean_dec_ref(v___x_165_);
v___x_167_ = l_Std_Time_Database_TZdb_parseTZIfFromDisk(v_path_158_, v_val_166_);
lean_dec_ref(v_path_158_);
return v___x_167_;
}
else
{
lean_object* v___x_168_; lean_object* v___x_170_; 
lean_dec(v___x_165_);
lean_dec_ref(v_path_158_);
v___x_168_ = lean_obj_once(&l_Std_Time_Database_TZdb_localRules___closed__1, &l_Std_Time_Database_TZdb_localRules___closed__1_once, _init_l_Std_Time_Database_TZdb_localRules___closed__1);
if (v_isShared_164_ == 0)
{
lean_ctor_set_tag(v___x_163_, 1);
lean_ctor_set(v___x_163_, 0, v___x_168_);
v___x_170_ = v___x_163_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
else
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
lean_dec_ref(v_path_158_);
v_a_173_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_160_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_160_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_localRules___boxed(lean_object* v_path_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Std_Time_Database_TZdb_localRules(v_path_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_readRulesFromDisk(lean_object* v_path_184_, lean_object* v_id_185_){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
lean_inc_ref(v_id_185_);
v___x_187_ = l_System_FilePath_join(v_path_184_, v_id_185_);
v___x_188_ = l_Std_Time_Database_TZdb_parseTZIfFromDisk(v___x_187_, v_id_185_);
lean_dec_ref(v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_readRulesFromDisk___boxed(lean_object* v_path_189_, lean_object* v_id_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_Time_Database_TZdb_readRulesFromDisk(v_path_189_, v_id_190_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_inst___lam__0(lean_object* v_db_193_){
_start:
{
lean_object* v_localPath_195_; lean_object* v___x_196_; 
v_localPath_195_ = lean_ctor_get(v_db_193_, 0);
lean_inc_ref(v_localPath_195_);
lean_dec_ref(v_db_193_);
v___x_196_ = l_Std_Time_Database_TZdb_localRules(v_localPath_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_inst___lam__0___boxed(lean_object* v_db_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Std_Time_Database_TZdb_inst___lam__0(v_db_197_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_inst___lam__1(lean_object* v___x_200_, lean_object* v_id_201_, lean_object* v___x_202_, lean_object* v_a_203_, lean_object* v_x_204_, lean_object* v___y_205_){
_start:
{
uint8_t v___x_207_; 
v___x_207_ = l_System_FilePath_pathExists(v_a_203_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; 
lean_dec_ref(v_a_203_);
lean_dec_ref(v_id_201_);
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_200_);
v___x_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
return v___x_209_;
}
else
{
lean_object* v___x_210_; 
lean_dec_ref(v___x_200_);
v___x_210_ = l_Std_Time_Database_TZdb_readRulesFromDisk(v_a_203_, v_id_201_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_221_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_221_ == 0)
{
v___x_213_ = v___x_210_;
v_isShared_214_ = v_isSharedCheck_221_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_210_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_221_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_219_; 
v___x_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_215_, 0, v_a_211_);
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v___x_202_);
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_217_);
v___x_219_ = v___x_213_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
v_a_222_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_210_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_210_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_inst___lam__1___boxed(lean_object* v___x_230_, lean_object* v_id_231_, lean_object* v___x_232_, lean_object* v_a_233_, lean_object* v_x_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Std_Time_Database_TZdb_inst___lam__1(v___x_230_, v_id_231_, v___x_232_, v_a_233_, v_x_234_, v___y_235_);
lean_dec_ref(v___y_235_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_inst___lam__2(lean_object* v___x_244_, lean_object* v_db_245_, lean_object* v_id_246_){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l_Std_Time_Database_TZdb_inst___lam__2___closed__0));
v___x_249_ = lean_io_getenv(v___x_248_);
if (lean_obj_tag(v___x_249_) == 1)
{
lean_object* v_val_250_; lean_object* v___x_251_; 
lean_dec_ref(v_db_245_);
lean_dec_ref(v___x_244_);
v_val_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_val_250_);
lean_dec_ref(v___x_249_);
v___x_251_ = l_Std_Time_Database_TZdb_readRulesFromDisk(v_val_250_, v_id_246_);
return v___x_251_;
}
else
{
lean_object* v_zonesPaths_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___f_255_; size_t v_sz_256_; size_t v___x_257_; lean_object* v___x_622__overap_258_; lean_object* v___x_259_; 
lean_dec(v___x_249_);
v_zonesPaths_252_ = lean_ctor_get(v_db_245_, 1);
lean_inc_ref(v_zonesPaths_252_);
lean_dec_ref(v_db_245_);
v___x_253_ = lean_box(0);
v___x_254_ = ((lean_object*)(l_Std_Time_Database_TZdb_inst___lam__2___closed__1));
lean_inc_ref(v_id_246_);
v___f_255_ = lean_alloc_closure((void*)(l_Std_Time_Database_TZdb_inst___lam__1___boxed), 7, 3);
lean_closure_set(v___f_255_, 0, v___x_254_);
lean_closure_set(v___f_255_, 1, v_id_246_);
lean_closure_set(v___f_255_, 2, v___x_253_);
v_sz_256_ = lean_array_size(v_zonesPaths_252_);
v___x_257_ = ((size_t)0ULL);
v___x_622__overap_258_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_244_, v_zonesPaths_252_, v___f_255_, v_sz_256_, v___x_257_, v___x_254_);
v___x_259_ = lean_apply_1(v___x_622__overap_258_, lean_box(0));
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_277_; 
v_a_260_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_277_ == 0)
{
v___x_262_ = v___x_259_;
v_isShared_263_ = v_isSharedCheck_277_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_259_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_277_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v_fst_264_; 
v_fst_264_ = lean_ctor_get(v_a_260_, 0);
lean_inc(v_fst_264_);
lean_dec(v_a_260_);
if (lean_obj_tag(v_fst_264_) == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_265_ = ((lean_object*)(l_Std_Time_Database_TZdb_inst___lam__2___closed__2));
v___x_266_ = lean_string_append(v___x_265_, v_id_246_);
lean_dec_ref(v_id_246_);
v___x_267_ = ((lean_object*)(l_Std_Time_Database_TZdb_inst___lam__2___closed__3));
v___x_268_ = lean_string_append(v___x_266_, v___x_267_);
v___x_269_ = lean_mk_io_user_error(v___x_268_);
if (v_isShared_263_ == 0)
{
lean_ctor_set_tag(v___x_262_, 1);
lean_ctor_set(v___x_262_, 0, v___x_269_);
v___x_271_ = v___x_262_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
else
{
lean_object* v_val_273_; lean_object* v___x_275_; 
lean_dec_ref(v_id_246_);
v_val_273_ = lean_ctor_get(v_fst_264_, 0);
lean_inc(v_val_273_);
lean_dec_ref(v_fst_264_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v_val_273_);
v___x_275_ = v___x_262_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_val_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec_ref(v_id_246_);
v_a_278_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_259_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_259_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_TZdb_inst___lam__2___boxed(lean_object* v___x_286_, lean_object* v_db_287_, lean_object* v_id_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Std_Time_Database_TZdb_inst___lam__2(v___x_286_, v_db_287_, v_id_288_);
return v_res_290_;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_inst___closed__1(void){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_instMonadEIO(lean_box(0));
return v___x_292_;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_inst___closed__2(void){
_start:
{
lean_object* v___x_293_; lean_object* v___f_294_; 
v___x_293_ = lean_obj_once(&l_Std_Time_Database_TZdb_inst___closed__1, &l_Std_Time_Database_TZdb_inst___closed__1_once, _init_l_Std_Time_Database_TZdb_inst___closed__1);
v___f_294_ = lean_alloc_closure((void*)(l_Std_Time_Database_TZdb_inst___lam__2___boxed), 4, 1);
lean_closure_set(v___f_294_, 0, v___x_293_);
return v___f_294_;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_inst___closed__3(void){
_start:
{
lean_object* v___f_295_; lean_object* v___f_296_; lean_object* v___x_297_; 
v___f_295_ = ((lean_object*)(l_Std_Time_Database_TZdb_inst___closed__0));
v___f_296_ = lean_obj_once(&l_Std_Time_Database_TZdb_inst___closed__2, &l_Std_Time_Database_TZdb_inst___closed__2_once, _init_l_Std_Time_Database_TZdb_inst___closed__2);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v___f_296_);
lean_ctor_set(v___x_297_, 1, v___f_295_);
return v___x_297_;
}
}
static lean_object* _init_l_Std_Time_Database_TZdb_inst(void){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = lean_obj_once(&l_Std_Time_Database_TZdb_inst___closed__3, &l_Std_Time_Database_TZdb_inst___closed__3_once, _init_l_Std_Time_Database_TZdb_inst___closed__3);
return v___x_298_;
}
}
lean_object* runtime_initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_Database_TZdb(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Zoned_Database_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_Database_TZdb_inst = _init_l_Std_Time_Database_TZdb_inst();
lean_mark_persistent(l_Std_Time_Database_TZdb_inst);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Zoned_Database_TZdb(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_Database_TZdb(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Zoned_Database_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database_TZdb(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Zoned_Database_TZdb(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Zoned_Database_TZdb(builtin);
}
#ifdef __cplusplus
}
#endif
