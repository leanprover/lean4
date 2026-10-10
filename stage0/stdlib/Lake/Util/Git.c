// Lean compiler output
// Module: Lake.Util.Git
// Imports: public import Init.Data.ToString public import Lake.Util.Proc import Init.Data.String.TakeDrop import Init.Data.String.Search import Lake.Util.String
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lake_captureProc_x3f(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_testProc(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lake_mkCmdLog(lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t l_Lake_isHex(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* l_Lake_captureProc_x27(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static const lean_string_object l_Lake_Git_defaultRemote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "origin"};
static const lean_object* l_Lake_Git_defaultRemote___closed__0 = (const lean_object*)&l_Lake_Git_defaultRemote___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Git_defaultRemote = (const lean_object*)&l_Lake_Git_defaultRemote___closed__0_value;
static const lean_string_object l_Lake_Git_upstreamBranch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "master"};
static const lean_object* l_Lake_Git_upstreamBranch___closed__0 = (const lean_object*)&l_Lake_Git_upstreamBranch___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Git_upstreamBranch = (const lean_object*)&l_Lake_Git_upstreamBranch___closed__0_value;
static const lean_string_object l_Lake_Git_filterUrl_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ".git"};
static const lean_object* l_Lake_Git_filterUrl_x3f___closed__0 = (const lean_object*)&l_Lake_Git_filterUrl_x3f___closed__0_value;
static const lean_string_object l_Lake_Git_filterUrl_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "git"};
static const lean_object* l_Lake_Git_filterUrl_x3f___closed__1 = (const lean_object*)&l_Lake_Git_filterUrl_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Git_isFullObjectName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object*);
static const lean_string_object l_Lake_GitRev_head___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Lake_GitRev_head___closed__0 = (const lean_object*)&l_Lake_GitRev_head___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRev_head = (const lean_object*)&l_Lake_GitRev_head___closed__0_value;
static const lean_string_object l_Lake_GitRev_fetchHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "FETCH_HEAD"};
static const lean_object* l_Lake_GitRev_fetchHead___closed__0 = (const lean_object*)&l_Lake_GitRev_fetchHead___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRev_fetchHead = (const lean_object*)&l_Lake_GitRev_fetchHead___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_GitRev_isFullSha1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRev_isFullSha1___boxed(lean_object*);
static const lean_string_object l_Lake_GitRev_withRemote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Lake_GitRev_withRemote___closed__0 = (const lean_object*)&l_Lake_GitRev_withRemote___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRev_withRemote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRev_withRemote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_instCoeFilePath___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_instCoeFilePath___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_GitRepo_instCoeFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_GitRepo_instCoeFilePath___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_GitRepo_instCoeFilePath___closed__0 = (const lean_object*)&l_Lake_GitRepo_instCoeFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRepo_instCoeFilePath = (const lean_object*)&l_Lake_GitRepo_instCoeFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRepo_instToString = (const lean_object*)&l_Lake_GitRepo_instCoeFilePath___closed__0_value;
static const lean_string_object l_Lake_GitRepo_cwd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_GitRepo_cwd___closed__0 = (const lean_object*)&l_Lake_GitRepo_cwd___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRepo_cwd = (const lean_object*)&l_Lake_GitRepo_cwd___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_GitRepo_dirExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_GitRepo_gitExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_gitExists___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_GitRepo_captureGit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_GitRepo_captureGit___closed__0 = (const lean_object*)&l_Lake_GitRepo_captureGit___closed__0_value;
static const lean_array_object l_Lake_GitRepo_captureGit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_GitRepo_captureGit___closed__1 = (const lean_object*)&l_Lake_GitRepo_captureGit___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_GitRepo_testGit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stderr:\n"};
static const lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1___closed__0 = (const lean_object*)&l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stdout:\n"};
static const lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__0 = (const lean_object*)&l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__0_value;
static const lean_string_object l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "failed to execute 'git': "};
static const lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__1 = (const lean_object*)&l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_clone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clone"};
static const lean_object* l_Lake_GitRepo_clone___closed__0 = (const lean_object*)&l_Lake_GitRepo_clone___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_clone___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_clone___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_quietInit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "init"};
static const lean_object* l_Lake_GitRepo_quietInit___closed__0 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__0_value;
static const lean_string_object l_Lake_GitRepo_quietInit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-q"};
static const lean_object* l_Lake_GitRepo_quietInit___closed__1 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__1_value;
static const lean_array_object l_Lake_GitRepo_quietInit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_quietInit___closed__0_value),((lean_object*)&l_Lake_GitRepo_quietInit___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_quietInit___closed__2 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_bareInit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--bare"};
static const lean_object* l_Lake_GitRepo_bareInit___closed__0 = (const lean_object*)&l_Lake_GitRepo_bareInit___closed__0_value;
static const lean_array_object l_Lake_GitRepo_bareInit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_Lake_GitRepo_quietInit___closed__0_value),((lean_object*)&l_Lake_GitRepo_bareInit___closed__0_value),((lean_object*)&l_Lake_GitRepo_quietInit___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_bareInit___closed__1 = (const lean_object*)&l_Lake_GitRepo_bareInit___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_bareInit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_bareInit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_insideWorkTree___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rev-parse"};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__0 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__0_value;
static const lean_string_object l_Lake_GitRepo_insideWorkTree___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "--is-inside-work-tree"};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__1 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__1_value;
static const lean_array_object l_Lake_GitRepo_insideWorkTree___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__0_value),((lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__2 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__2_value;
LEAN_EXPORT uint8_t l_Lake_GitRepo_insideWorkTree(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_insideWorkTree___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_fetch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "fetch"};
static const lean_object* l_Lake_GitRepo_fetch___closed__0 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__0_value;
static const lean_string_object l_Lake_GitRepo_fetch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--tags"};
static const lean_object* l_Lake_GitRepo_fetch___closed__1 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__1_value;
static const lean_string_object l_Lake_GitRepo_fetch___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "--force"};
static const lean_object* l_Lake_GitRepo_fetch___closed__2 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__2_value;
static lean_once_cell_t l_Lake_GitRepo_fetch___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetch___closed__3;
static lean_once_cell_t l_Lake_GitRepo_fetch___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetch___closed__4;
static lean_once_cell_t l_Lake_GitRepo_fetch___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetch___closed__5;
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_addWorktreeDetach___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "worktree"};
static const lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__0 = (const lean_object*)&l_Lake_GitRepo_addWorktreeDetach___closed__0_value;
static const lean_string_object l_Lake_GitRepo_addWorktreeDetach___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__1 = (const lean_object*)&l_Lake_GitRepo_addWorktreeDetach___closed__1_value;
static const lean_string_object l_Lake_GitRepo_addWorktreeDetach___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--detach"};
static const lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__2 = (const lean_object*)&l_Lake_GitRepo_addWorktreeDetach___closed__2_value;
static lean_once_cell_t l_Lake_GitRepo_addWorktreeDetach___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__3;
static lean_once_cell_t l_Lake_GitRepo_addWorktreeDetach___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__4;
static lean_once_cell_t l_Lake_GitRepo_addWorktreeDetach___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__5;
LEAN_EXPORT lean_object* l_Lake_GitRepo_addWorktreeDetach(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_addWorktreeDetach___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_checkoutBranch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "checkout"};
static const lean_object* l_Lake_GitRepo_checkoutBranch___closed__0 = (const lean_object*)&l_Lake_GitRepo_checkoutBranch___closed__0_value;
static const lean_string_object l_Lake_GitRepo_checkoutBranch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-B"};
static const lean_object* l_Lake_GitRepo_checkoutBranch___closed__1 = (const lean_object*)&l_Lake_GitRepo_checkoutBranch___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_checkoutBranch___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__2;
static lean_once_cell_t l_Lake_GitRepo_checkoutBranch___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_checkoutDetach___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "--"};
static const lean_object* l_Lake_GitRepo_checkoutDetach___closed__0 = (const lean_object*)&l_Lake_GitRepo_checkoutDetach___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_checkoutDetach___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutDetach___closed__1;
static lean_once_cell_t l_Lake_GitRepo_checkoutDetach___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutDetach___closed__2;
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_gcAuto___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gc"};
static const lean_object* l_Lake_GitRepo_gcAuto___closed__0 = (const lean_object*)&l_Lake_GitRepo_gcAuto___closed__0_value;
static const lean_string_object l_Lake_GitRepo_gcAuto___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--auto"};
static const lean_object* l_Lake_GitRepo_gcAuto___closed__1 = (const lean_object*)&l_Lake_GitRepo_gcAuto___closed__1_value;
static const lean_array_object l_Lake_GitRepo_gcAuto___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_gcAuto___closed__0_value),((lean_object*)&l_Lake_GitRepo_gcAuto___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_gcAuto___closed__2 = (const lean_object*)&l_Lake_GitRepo_gcAuto___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_gcAuto(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_gcAuto___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_clean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clean"};
static const lean_object* l_Lake_GitRepo_clean___closed__0 = (const lean_object*)&l_Lake_GitRepo_clean___closed__0_value;
static const lean_string_object l_Lake_GitRepo_clean___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "-xf"};
static const lean_object* l_Lake_GitRepo_clean___closed__1 = (const lean_object*)&l_Lake_GitRepo_clean___closed__1_value;
static const lean_array_object l_Lake_GitRepo_clean___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_clean___closed__0_value),((lean_object*)&l_Lake_GitRepo_clean___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_clean___closed__2 = (const lean_object*)&l_Lake_GitRepo_clean___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_resolveRevision_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--verify"};
static const lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_resolveRevision_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_resolveRevision_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "--end-of-options"};
static const lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_resolveRevision_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_resolveRevision_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_resolveRevision_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__3;
static lean_once_cell_t l_Lake_GitRepo_resolveRevision_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_findCommit_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "^{commit}"};
static const lean_object* l_Lake_GitRepo_findCommit_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_findCommit_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_findCommit_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findCommit_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_resolveRevision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = ": revision not found '"};
static const lean_object* l_Lake_GitRepo_resolveRevision___closed__0 = (const lean_object*)&l_Lake_GitRepo_resolveRevision___closed__0_value;
static const lean_string_object l_Lake_GitRepo_resolveRevision___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lake_GitRepo_resolveRevision___closed__1 = (const lean_object*)&l_Lake_GitRepo_resolveRevision___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getHeadRevision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 114, .m_capacity = 114, .m_length = 113, .m_data = ": could not resolve 'HEAD' to a commit; the repository may be corrupt, so you may need to remove it and try again"};
static const lean_object* l_Lake_GitRepo_getHeadRevision___closed__0 = (const lean_object*)&l_Lake_GitRepo_getHeadRevision___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_fetchRevision_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "--filter=tree:0"};
static const lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_fetchRevision_x3f___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_fetchRevision_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__1;
static lean_once_cell_t l_Lake_GitRepo_fetchRevision_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_fetchRevision_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__3;
static lean_once_cell_t l_Lake_GitRepo_fetchRevision_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__4;
static const lean_string_object l_Lake_GitRepo_fetchRevision_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 110, .m_capacity = 110, .m_length = 109, .m_data = ": could not resolve 'FETCH_HEAD' to a commit after fetching; this may be an issue with Lake; please report it"};
static const lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__5 = (const lean_object*)&l_Lake_GitRepo_fetchRevision_x3f___closed__5_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetchRevision_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetchRevision_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getHeadRevisions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rev-list"};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__0 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__0_value;
static const lean_array_object l_Lake_GitRepo_getHeadRevisions___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__0_value),((lean_object*)&l_Lake_GitRev_head___closed__0_value)}};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__1 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__1_value;
static const lean_string_object l_Lake_GitRepo_getHeadRevisions___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-n"};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__2 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__2_value;
static lean_once_cell_t l_Lake_GitRepo_getHeadRevisions___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_getHeadRevisions___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_branchExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "show-ref"};
static const lean_object* l_Lake_GitRepo_branchExists___closed__0 = (const lean_object*)&l_Lake_GitRepo_branchExists___closed__0_value;
static const lean_string_object l_Lake_GitRepo_branchExists___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "refs/heads/"};
static const lean_object* l_Lake_GitRepo_branchExists___closed__1 = (const lean_object*)&l_Lake_GitRepo_branchExists___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_branchExists___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_branchExists___closed__2;
static lean_once_cell_t l_Lake_GitRepo_branchExists___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_branchExists___closed__3;
LEAN_EXPORT uint8_t l_Lake_GitRepo_branchExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_GitRepo_revisionExists___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_revisionExists___closed__0;
static lean_once_cell_t l_Lake_GitRepo_revisionExists___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_revisionExists___closed__1;
LEAN_EXPORT uint8_t l_Lake_GitRepo_revisionExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getTags___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "tag"};
static const lean_object* l_Lake_GitRepo_getTags___closed__0 = (const lean_object*)&l_Lake_GitRepo_getTags___closed__0_value;
static const lean_array_object l_Lake_GitRepo_getTags___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lake_GitRepo_getTags___closed__0_value)}};
static const lean_object* l_Lake_GitRepo_getTags___closed__1 = (const lean_object*)&l_Lake_GitRepo_getTags___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_findTag_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "describe"};
static const lean_object* l_Lake_GitRepo_findTag_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_findTag_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_findTag_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "--exact-match"};
static const lean_object* l_Lake_GitRepo_findTag_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_findTag_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_findTag_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_findTag_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__3;
static lean_once_cell_t l_Lake_GitRepo_findTag_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getRemoteUrl_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "remote"};
static const lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_getRemoteUrl_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_getRemoteUrl_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "get-url"};
static const lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_getRemoteUrl_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_getRemoteUrl_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_getRemoteUrl_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_GitRepo_addRemote___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addRemote___closed__0;
static lean_once_cell_t l_Lake_GitRepo_addRemote___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addRemote___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_addRemote(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_addRemote___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_setRemoteUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "set-url"};
static const lean_object* l_Lake_GitRepo_setRemoteUrl___closed__0 = (const lean_object*)&l_Lake_GitRepo_setRemoteUrl___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_setRemoteUrl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_setRemoteUrl___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_setRemoteUrl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_setRemoteUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_pruneRemote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "prune"};
static const lean_object* l_Lake_GitRepo_pruneRemote___closed__0 = (const lean_object*)&l_Lake_GitRepo_pruneRemote___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_pruneRemote___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_pruneRemote___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_pruneRemote(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_pruneRemote___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_hasNoDiff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "diff"};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__0 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__0_value;
static const lean_string_object l_Lake_GitRepo_hasNoDiff___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "--exit-code"};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__1 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__1_value;
static const lean_array_object l_Lake_GitRepo_hasNoDiff___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__0_value),((lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__1_value),((lean_object*)&l_Lake_GitRev_head___closed__0_value)}};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__2 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__2_value;
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasNoDiff(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasDiff(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Git_filterUrl_x3f(lean_object* v_url_7_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_22_ = lean_string_utf8_byte_size(v_url_7_);
v___x_23_ = lean_unsigned_to_nat(3u);
v___x_24_ = lean_nat_dec_le(v___x_23_, v___x_22_);
if (v___x_24_ == 0)
{
goto v___jp_8_;
}
else
{
lean_object* v___x_25_; lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_25_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_26_ = lean_unsigned_to_nat(0u);
v___x_27_ = lean_string_memcmp(v_url_7_, v___x_25_, v___x_26_, v___x_26_, v___x_23_);
if (v___x_27_ == 0)
{
goto v___jp_8_;
}
else
{
lean_object* v___x_28_; 
lean_dec_ref(v_url_7_);
v___x_28_ = lean_box(0);
return v___x_28_;
}
}
v___jp_8_:
{
lean_object* v___x_9_; lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_9_ = lean_string_utf8_byte_size(v_url_7_);
v___x_10_ = lean_unsigned_to_nat(4u);
v___x_11_ = lean_nat_dec_le(v___x_10_, v___x_9_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; 
v___x_12_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_12_, 0, v_url_7_);
return v___x_12_;
}
else
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_13_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__0));
v___x_14_ = lean_unsigned_to_nat(0u);
v___x_15_ = lean_nat_sub(v___x_9_, v___x_10_);
v___x_16_ = lean_string_memcmp(v_url_7_, v___x_13_, v___x_15_, v___x_14_, v___x_10_);
lean_dec(v___x_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; 
v___x_17_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_17_, 0, v_url_7_);
return v___x_17_;
}
else
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
lean_inc_ref(v_url_7_);
v___x_18_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_18_, 0, v_url_7_);
lean_ctor_set(v___x_18_, 1, v___x_14_);
lean_ctor_set(v___x_18_, 2, v___x_9_);
v___x_19_ = l_String_Slice_Pos_prevn(v___x_18_, v___x_9_, v___x_10_);
lean_dec_ref_known(v___x_18_, 3);
v___x_20_ = lean_string_utf8_extract_fast(v_url_7_, v___x_14_, v___x_19_);
lean_dec(v___x_19_);
lean_dec_ref(v_url_7_);
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
return v___x_21_;
}
}
}
}
}
uint8_t l_Lake_Git_isFullObjectName(lean_object* v_rev_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; 
v___x_30_ = lean_string_utf8_byte_size(v_rev_29_);
v___x_31_ = lean_unsigned_to_nat(40u);
v___x_32_ = lean_nat_dec_eq(v___x_30_, v___x_31_);
if (v___x_32_ == 0)
{
return v___x_32_;
}
else
{
uint8_t v___x_33_; 
v___x_33_ = l_Lake_isHex(v_rev_29_);
return v___x_33_;
}
}
}
LEAN_EXPORT void l_Lake_Git_isFullObjectName_0interp(lean_interpreter_value* stack)
{
lean_object* v_rev_29_ = stack[0].m_obj;
uint8_t v_res_34_;
v_res_34_ = l_Lake_Git_isFullObjectName(v_rev_29_);
stack->m_num = v_res_34_;
}
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object* v_rev_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = l_Lake_Git_isFullObjectName(v_rev_35_);
lean_dec_ref(v_rev_35_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
uint8_t l_Lake_GitRev_isFullSha1(lean_object* v_rev_42_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_43_ = lean_string_utf8_byte_size(v_rev_42_);
v___x_44_ = lean_unsigned_to_nat(40u);
v___x_45_ = lean_nat_dec_eq(v___x_43_, v___x_44_);
if (v___x_45_ == 0)
{
return v___x_45_;
}
else
{
uint8_t v___x_46_; 
v___x_46_ = l_Lake_isHex(v_rev_42_);
return v___x_46_;
}
}
}
LEAN_EXPORT void l_Lake_GitRev_isFullSha1_0interp(lean_interpreter_value* stack)
{
lean_object* v_rev_42_ = stack[0].m_obj;
uint8_t v_res_47_;
v_res_47_ = l_Lake_GitRev_isFullSha1(v_rev_42_);
stack->m_num = v_res_47_;
}
LEAN_EXPORT lean_object* l_Lake_GitRev_isFullSha1___boxed(lean_object* v_rev_48_){
_start:
{
uint8_t v_res_49_; lean_object* v_r_50_; 
v_res_49_ = l_Lake_GitRev_isFullSha1(v_rev_48_);
lean_dec_ref(v_rev_48_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRev_withRemote(lean_object* v_remote_52_, lean_object* v_rev_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = ((lean_object*)(l_Lake_GitRev_withRemote___closed__0));
v___x_55_ = lean_string_append(v_remote_52_, v___x_54_);
v___x_56_ = lean_string_append(v___x_55_, v_rev_53_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRev_withRemote___boxed(lean_object* v_remote_57_, lean_object* v_rev_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lake_GitRev_withRemote(v_remote_57_, v_rev_58_);
lean_dec_ref(v_rev_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_instCoeFilePath___lam__0(lean_object* v_x_60_){
_start:
{
lean_inc_ref(v_x_60_);
return v_x_60_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_instCoeFilePath___lam__0___boxed(lean_object* v_x_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lake_GitRepo_instCoeFilePath___lam__0(v_x_61_);
lean_dec_ref(v_x_61_);
return v_res_62_;
}
}
uint8_t l_Lake_GitRepo_dirExists(lean_object* v_repo_68_){
_start:
{
uint8_t v___x_70_; 
v___x_70_ = l_System_FilePath_isDir(v_repo_68_);
return v___x_70_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_dirExists_0interp(lean_interpreter_value* stack)
{
lean_object* v_repo_68_ = stack[0].m_obj;
uint8_t v_res_71_;
v_res_71_ = l_Lake_GitRepo_dirExists(v_repo_68_);
stack->m_num = v_res_71_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object* v_repo_72_, lean_object* v_a_73_){
_start:
{
uint8_t v_res_74_; lean_object* v_r_75_; 
v_res_74_ = l_Lake_GitRepo_dirExists(v_repo_72_);
lean_dec_ref(v_repo_72_);
v_r_75_ = lean_box(v_res_74_);
return v_r_75_;
}
}
uint8_t l_Lake_GitRepo_gitExists(lean_object* v_repo_76_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_78_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__0));
v___x_79_ = l_System_FilePath_join(v_repo_76_, v___x_78_);
v___x_80_ = l_System_FilePath_pathExists(v___x_79_);
lean_dec_ref(v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_gitExists_0interp(lean_interpreter_value* stack)
{
lean_object* v_repo_76_ = stack[0].m_obj;
uint8_t v_res_81_;
v_res_81_ = l_Lake_GitRepo_gitExists(v_repo_76_);
stack->m_num = v_res_81_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_gitExists___boxed(lean_object* v_repo_82_, lean_object* v_a_83_){
_start:
{
uint8_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = l_Lake_GitRepo_gitExists(v_repo_82_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
lean_object* l_Lake_GitRepo_captureGit(lean_object* v_args_90_, lean_object* v_repo_91_, lean_object* v_a_92_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; uint8_t v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_94_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_95_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_96_, 0, v_repo_91_);
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_99_ = 1;
v___x_100_ = 0;
v___x_101_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_101_, 0, v___x_94_);
lean_ctor_set(v___x_101_, 1, v___x_95_);
lean_ctor_set(v___x_101_, 2, v_args_90_);
lean_ctor_set(v___x_101_, 3, v___x_96_);
lean_ctor_set(v___x_101_, 4, v___x_98_);
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*5, v___x_99_);
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*5 + 1, v___x_100_);
v___x_102_ = l_Lake_captureProc_x27(v___x_101_, v_a_92_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_119_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
v_a_104_ = lean_ctor_get(v___x_102_, 1);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_119_ == 0)
{
v___x_106_ = v___x_102_;
v_isShared_107_ = v_isSharedCheck_119_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_inc(v_a_103_);
lean_dec(v___x_102_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_119_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v_stdout_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v_str_112_; lean_object* v_startInclusive_113_; lean_object* v_endExclusive_114_; lean_object* v___x_115_; lean_object* v___x_117_; 
v_stdout_108_ = lean_ctor_get(v_a_103_, 0);
lean_inc_ref(v_stdout_108_);
lean_dec(v_a_103_);
v___x_109_ = lean_string_utf8_byte_size(v_stdout_108_);
v___x_110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_110_, 0, v_stdout_108_);
lean_ctor_set(v___x_110_, 1, v___x_97_);
lean_ctor_set(v___x_110_, 2, v___x_109_);
v___x_111_ = l_String_Slice_trimAscii(v___x_110_);
v_str_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc_ref(v_str_112_);
v_startInclusive_113_ = lean_ctor_get(v___x_111_, 1);
lean_inc(v_startInclusive_113_);
v_endExclusive_114_ = lean_ctor_get(v___x_111_, 2);
lean_inc(v_endExclusive_114_);
lean_dec_ref(v___x_111_);
v___x_115_ = lean_string_utf8_extract_fast(v_str_112_, v_startInclusive_113_, v_endExclusive_114_);
lean_dec(v_endExclusive_114_);
lean_dec(v_startInclusive_113_);
lean_dec_ref(v_str_112_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v___x_115_);
v___x_117_ = v___x_106_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_a_104_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
else
{
lean_object* v_a_120_; lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
v_a_120_ = lean_ctor_get(v___x_102_, 0);
v_a_121_ = lean_ctor_get(v___x_102_, 1);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_102_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_inc(v_a_120_);
lean_dec(v___x_102_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_120_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_GitRepo_captureGit_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_90_ = stack[0].m_obj;
lean_object* v_repo_91_ = stack[1].m_obj;
lean_object* v_a_92_ = stack[2].m_obj;
lean_object* v_res_129_;
v_res_129_ = l_Lake_GitRepo_captureGit(v_args_90_, v_repo_91_, v_a_92_);
stack->m_obj
 = v_res_129_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit___boxed(lean_object* v_args_130_, lean_object* v_repo_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lake_GitRepo_captureGit(v_args_130_, v_repo_131_, v_a_132_);
return v_res_134_;
}
}
lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object* v_args_135_, lean_object* v_repo_136_){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; uint8_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_138_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_139_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_140_, 0, v_repo_136_);
v___x_141_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_142_ = 1;
v___x_143_ = 0;
v___x_144_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_144_, 0, v___x_138_);
lean_ctor_set(v___x_144_, 1, v___x_139_);
lean_ctor_set(v___x_144_, 2, v_args_135_);
lean_ctor_set(v___x_144_, 3, v___x_140_);
lean_ctor_set(v___x_144_, 4, v___x_141_);
lean_ctor_set_uint8(v___x_144_, sizeof(void*)*5, v___x_142_);
lean_ctor_set_uint8(v___x_144_, sizeof(void*)*5 + 1, v___x_143_);
v___x_145_ = l_Lake_captureProc_x3f(v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_captureGit_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_135_ = stack[0].m_obj;
lean_object* v_repo_136_ = stack[1].m_obj;
lean_object* v_res_146_;
v_res_146_ = l_Lake_GitRepo_captureGit_x3f(v_args_135_, v_repo_136_);
stack->m_obj
 = v_res_146_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f___boxed(lean_object* v_args_147_, lean_object* v_repo_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lake_GitRepo_captureGit_x3f(v_args_147_, v_repo_148_);
return v_res_150_;
}
}
lean_object* l_Lake_GitRepo_execGit(lean_object* v_args_151_, lean_object* v_repo_152_, lean_object* v_a_153_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; uint8_t v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_155_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_156_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_157_, 0, v_repo_152_);
v___x_158_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_159_ = 1;
v___x_160_ = 0;
v___x_161_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_161_, 0, v___x_155_);
lean_ctor_set(v___x_161_, 1, v___x_156_);
lean_ctor_set(v___x_161_, 2, v_args_151_);
lean_ctor_set(v___x_161_, 3, v___x_157_);
lean_ctor_set(v___x_161_, 4, v___x_158_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*5, v___x_159_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*5 + 1, v___x_160_);
v___x_162_ = lean_box(0);
v___x_163_ = l_Lake_proc(v___x_161_, v___x_159_, v___x_162_, v_a_153_);
return v___x_163_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_execGit_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_151_ = stack[0].m_obj;
lean_object* v_repo_152_ = stack[1].m_obj;
lean_object* v_a_153_ = stack[2].m_obj;
lean_object* v_res_164_;
v_res_164_ = l_Lake_GitRepo_execGit(v_args_151_, v_repo_152_, v_a_153_);
stack->m_obj
 = v_res_164_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit___boxed(lean_object* v_args_165_, lean_object* v_repo_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lake_GitRepo_execGit(v_args_165_, v_repo_166_, v_a_167_);
return v_res_169_;
}
}
uint8_t l_Lake_GitRepo_testGit(lean_object* v_args_170_, lean_object* v_repo_171_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; uint8_t v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_173_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_174_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_175_, 0, v_repo_171_);
v___x_176_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_177_ = 1;
v___x_178_ = 0;
v___x_179_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_179_, 0, v___x_173_);
lean_ctor_set(v___x_179_, 1, v___x_174_);
lean_ctor_set(v___x_179_, 2, v_args_170_);
lean_ctor_set(v___x_179_, 3, v___x_175_);
lean_ctor_set(v___x_179_, 4, v___x_176_);
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*5, v___x_177_);
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*5 + 1, v___x_178_);
v___x_180_ = l_Lake_testProc(v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_testGit_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_170_ = stack[0].m_obj;
lean_object* v_repo_171_ = stack[1].m_obj;
uint8_t v_res_181_;
v_res_181_ = l_Lake_GitRepo_testGit(v_args_170_, v_repo_171_);
stack->m_num = v_res_181_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit___boxed(lean_object* v_args_182_, lean_object* v_repo_183_, lean_object* v_a_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l_Lake_GitRepo_testGit(v_args_182_, v_repo_183_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0(uint8_t v___x_187_, uint8_t v___x_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
if (v___x_187_ == 0)
{
uint8_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_192_ = 1;
v___x_193_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_193_, 0, v___y_189_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*1, v___x_192_);
v___x_194_ = lean_box(0);
v___x_195_ = lean_array_push(v___y_190_, v___x_193_);
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_194_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
return v___x_196_;
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_197_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_197_, 0, v___y_189_);
lean_ctor_set_uint8(v___x_197_, sizeof(void*)*1, v___x_188_);
v___x_198_ = lean_box(0);
v___x_199_ = lean_array_push(v___y_190_, v___x_197_);
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_198_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
return v___x_200_;
}
}
}
LEAN_EXPORT void l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_187_ = stack[0].m_num;
uint8_t v___x_188_ = stack[1].m_num;
lean_object* v___y_189_ = stack[2].m_obj;
lean_object* v___y_190_ = stack[3].m_obj;
lean_object* v_res_201_;
v_res_201_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0(v___x_187_, v___x_188_, v___y_189_, v___y_190_);
stack->m_obj
 = v_res_201_;
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0___boxed(lean_object* v___x_202_, lean_object* v___x_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
uint8_t v___x_1996__boxed_207_; uint8_t v___x_1997__boxed_208_; lean_object* v_res_209_; 
v___x_1996__boxed_207_ = lean_unbox(v___x_202_);
v___x_1997__boxed_208_ = lean_unbox(v___x_203_);
v_res_209_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0(v___x_1996__boxed_207_, v___x_1997__boxed_208_, v___y_204_, v___y_205_);
return v_res_209_;
}
}
lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1(lean_object* v_stderr_211_, lean_object* v___x_212_, lean_object* v___y_213_, lean_object* v_____r_214_, lean_object* v___y_215_){
_start:
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = lean_string_utf8_byte_size(v_stderr_211_);
v___x_218_ = lean_nat_dec_eq(v___x_217_, v___x_212_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_219_ = ((lean_object*)(l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1___closed__0));
v___x_220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_220_, 0, v_stderr_211_);
lean_ctor_set(v___x_220_, 1, v___x_212_);
lean_ctor_set(v___x_220_, 2, v___x_217_);
v___x_221_ = l_String_Slice_trimAscii(v___x_220_);
v___x_222_ = l_String_Slice_toString(v___x_221_);
lean_dec_ref(v___x_221_);
v___x_223_ = lean_string_append(v___x_219_, v___x_222_);
lean_dec_ref(v___x_222_);
v___x_224_ = lean_apply_3(v___y_213_, v___x_223_, v___y_215_, lean_box(0));
return v___x_224_;
}
else
{
lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec_ref(v___y_213_);
lean_dec(v___x_212_);
lean_dec_ref(v_stderr_211_);
v___x_225_ = lean_box(0);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___y_215_);
return v___x_226_;
}
}
}
LEAN_EXPORT void l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_stderr_211_ = stack[0].m_obj;
lean_object* v___x_212_ = stack[1].m_obj;
lean_object* v___y_213_ = stack[2].m_obj;
lean_object* v_____r_214_ = stack[3].m_obj;
lean_object* v___y_215_ = stack[4].m_obj;
lean_object* v_res_227_;
v_res_227_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1(v_stderr_211_, v___x_212_, v___y_213_, v_____r_214_, v___y_215_);
stack->m_obj
 = v_res_227_;
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1___boxed(lean_object* v_stderr_228_, lean_object* v___x_229_, lean_object* v___y_230_, lean_object* v_____r_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1(v_stderr_228_, v___x_229_, v___y_230_, v_____r_231_, v___y_232_);
return v_res_234_;
}
}
lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit(lean_object* v_args_237_, lean_object* v_repo_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_a_242_; lean_object* v_a_243_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; uint8_t v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_245_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_246_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_247_, 0, v_repo_238_);
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_250_ = 1;
v___x_251_ = 0;
v___x_252_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_252_, 0, v___x_245_);
lean_ctor_set(v___x_252_, 1, v___x_246_);
lean_ctor_set(v___x_252_, 2, v_args_237_);
lean_ctor_set(v___x_252_, 3, v___x_247_);
lean_ctor_set(v___x_252_, 4, v___x_249_);
lean_ctor_set_uint8(v___x_252_, sizeof(void*)*5, v___x_250_);
lean_ctor_set_uint8(v___x_252_, sizeof(void*)*5 + 1, v___x_251_);
v___x_253_ = lean_box(0);
v___x_254_ = lean_array_get_size(v_a_239_);
lean_inc_ref(v___x_252_);
v___x_255_ = l_Lake_mkCmdLog(v___x_252_);
v___x_256_ = 0;
v___x_257_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_257_, 0, v___x_255_);
lean_ctor_set_uint8(v___x_257_, sizeof(void*)*1, v___x_256_);
v___x_258_ = lean_array_push(v_a_239_, v___x_257_);
v___x_259_ = l_IO_Process_output(v___x_252_, v___x_253_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_a_260_; uint32_t v_exitCode_261_; lean_object* v_stdout_262_; lean_object* v_stderr_263_; uint32_t v___x_264_; uint8_t v___x_265_; lean_object* v___y_267_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___y_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v_a_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_a_260_);
lean_dec_ref_known(v___x_259_, 1);
v_exitCode_261_ = lean_ctor_get_uint32(v_a_260_, sizeof(void*)*2);
v_stdout_262_ = lean_ctor_get(v_a_260_, 0);
lean_inc_ref(v_stdout_262_);
v_stderr_263_ = lean_ctor_get(v_a_260_, 1);
lean_inc_ref(v_stderr_263_);
lean_dec(v_a_260_);
v___x_264_ = 0;
v___x_265_ = lean_uint32_dec_eq(v_exitCode_261_, v___x_264_);
v___x_280_ = lean_box(v___x_265_);
v___x_281_ = lean_box(v___x_256_);
v___y_282_ = lean_alloc_closure((void*)(l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0___boxed), 5, 2);
lean_closure_set(v___y_282_, 0, v___x_280_);
lean_closure_set(v___y_282_, 1, v___x_281_);
v___x_283_ = lean_string_utf8_byte_size(v_stdout_262_);
v___x_284_ = lean_nat_dec_eq(v___x_283_, v___x_248_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v_a_291_; lean_object* v_a_292_; lean_object* v___x_293_; 
v___x_285_ = ((lean_object*)(l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__0));
v___x_286_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_286_, 0, v_stdout_262_);
lean_ctor_set(v___x_286_, 1, v___x_248_);
lean_ctor_set(v___x_286_, 2, v___x_283_);
v___x_287_ = l_String_Slice_trimAscii(v___x_286_);
v___x_288_ = l_String_Slice_toString(v___x_287_);
lean_dec_ref(v___x_287_);
v___x_289_ = lean_string_append(v___x_285_, v___x_288_);
lean_dec_ref(v___x_288_);
v___x_290_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0(v___x_265_, v___x_256_, v___x_289_, v___x_258_);
v_a_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_291_);
v_a_292_ = lean_ctor_get(v___x_290_, 1);
lean_inc(v_a_292_);
lean_dec_ref(v___x_290_);
v___x_293_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1(v_stderr_263_, v___x_248_, v___y_282_, v_a_291_, v_a_292_);
v___y_267_ = v___x_293_;
goto v___jp_266_;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec_ref(v_stdout_262_);
v___x_294_ = lean_box(0);
v___x_295_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1(v_stderr_263_, v___x_248_, v___y_282_, v___x_294_, v___x_258_);
v___y_267_ = v___x_295_;
goto v___jp_266_;
}
v___jp_266_:
{
if (lean_obj_tag(v___y_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_276_; 
v_a_268_ = lean_ctor_get(v___y_267_, 1);
v_isSharedCheck_276_ = !lean_is_exclusive(v___y_267_);
if (v_isSharedCheck_276_ == 0)
{
lean_object* v_unused_277_; 
v_unused_277_ = lean_ctor_get(v___y_267_, 0);
lean_dec(v_unused_277_);
v___x_270_ = v___y_267_;
v_isShared_271_ = v_isSharedCheck_276_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___y_267_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_276_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_272_ = lean_box(v___x_265_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_272_);
v___x_274_ = v___x_270_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_a_268_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
else
{
lean_object* v_a_278_; lean_object* v_a_279_; 
v_a_278_ = lean_ctor_get(v___y_267_, 0);
lean_inc(v_a_278_);
v_a_279_ = lean_ctor_get(v___y_267_, 1);
lean_inc(v_a_279_);
lean_dec_ref_known(v___y_267_, 2);
v_a_242_ = v_a_278_;
v_a_243_ = v_a_279_;
goto v___jp_241_;
}
}
}
else
{
lean_object* v_a_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_a_296_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_a_296_);
lean_dec_ref_known(v___x_259_, 1);
v___x_297_ = ((lean_object*)(l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__1));
v___x_298_ = lean_io_error_to_string(v_a_296_);
v___x_299_ = lean_string_append(v___x_297_, v___x_298_);
lean_dec_ref(v___x_298_);
v___x_300_ = 3;
v___x_301_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_301_, 0, v___x_299_);
lean_ctor_set_uint8(v___x_301_, sizeof(void*)*1, v___x_300_);
v___x_302_ = lean_array_push(v___x_258_, v___x_301_);
v___x_303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_254_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
return v___x_303_;
}
v___jp_241_:
{
lean_object* v___x_244_; 
v___x_244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_244_, 0, v_a_242_);
lean_ctor_set(v___x_244_, 1, v_a_243_);
return v___x_244_;
}
}
}
LEAN_EXPORT void l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_237_ = stack[0].m_obj;
lean_object* v_repo_238_ = stack[1].m_obj;
lean_object* v_a_239_ = stack[2].m_obj;
lean_object* v_res_304_;
v_res_304_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit(v_args_237_, v_repo_238_, v_a_239_);
stack->m_obj
 = v_res_304_;
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___boxed(lean_object* v_args_305_, lean_object* v_repo_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit(v_args_305_, v_repo_306_, v_a_307_);
return v_res_309_;
}
}
static lean_object* _init_l_Lake_GitRepo_clone___closed__1(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_311_ = ((lean_object*)(l_Lake_GitRepo_clone___closed__0));
v___x_312_ = lean_unsigned_to_nat(3u);
v___x_313_ = lean_mk_empty_array_with_capacity(v___x_312_);
v___x_314_ = lean_array_push(v___x_313_, v___x_311_);
return v___x_314_;
}
}
lean_object* l_Lake_GitRepo_clone(lean_object* v_url_315_, lean_object* v_repo_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; uint8_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_319_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_320_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_321_ = lean_obj_once(&l_Lake_GitRepo_clone___closed__1, &l_Lake_GitRepo_clone___closed__1_once, _init_l_Lake_GitRepo_clone___closed__1);
v___x_322_ = lean_array_push(v___x_321_, v_url_315_);
v___x_323_ = lean_array_push(v___x_322_, v_repo_316_);
v___x_324_ = lean_box(0);
v___x_325_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_326_ = 1;
v___x_327_ = 0;
v___x_328_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_328_, 0, v___x_319_);
lean_ctor_set(v___x_328_, 1, v___x_320_);
lean_ctor_set(v___x_328_, 2, v___x_323_);
lean_ctor_set(v___x_328_, 3, v___x_324_);
lean_ctor_set(v___x_328_, 4, v___x_325_);
lean_ctor_set_uint8(v___x_328_, sizeof(void*)*5, v___x_326_);
lean_ctor_set_uint8(v___x_328_, sizeof(void*)*5 + 1, v___x_327_);
v___x_329_ = l_Lake_proc(v___x_328_, v___x_326_, v___x_324_, v_a_317_);
return v___x_329_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_clone_0interp(lean_interpreter_value* stack)
{
lean_object* v_url_315_ = stack[0].m_obj;
lean_object* v_repo_316_ = stack[1].m_obj;
lean_object* v_a_317_ = stack[2].m_obj;
lean_object* v_res_330_;
v_res_330_ = l_Lake_GitRepo_clone(v_url_315_, v_repo_316_, v_a_317_);
stack->m_obj
 = v_res_330_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone___boxed(lean_object* v_url_331_, lean_object* v_repo_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lake_GitRepo_clone(v_url_331_, v_repo_332_, v_a_333_);
return v_res_335_;
}
}
lean_object* l_Lake_GitRepo_quietInit(lean_object* v_repo_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; uint8_t v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_347_ = ((lean_object*)(l_Lake_GitRepo_quietInit___closed__2));
v___x_348_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_349_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_350_, 0, v_repo_344_);
v___x_351_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_352_ = 1;
v___x_353_ = 0;
v___x_354_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_354_, 0, v___x_348_);
lean_ctor_set(v___x_354_, 1, v___x_349_);
lean_ctor_set(v___x_354_, 2, v___x_347_);
lean_ctor_set(v___x_354_, 3, v___x_350_);
lean_ctor_set(v___x_354_, 4, v___x_351_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*5, v___x_352_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*5 + 1, v___x_353_);
v___x_355_ = lean_box(0);
v___x_356_ = l_Lake_proc(v___x_354_, v___x_352_, v___x_355_, v_a_345_);
return v___x_356_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_quietInit_0interp(lean_interpreter_value* stack)
{
lean_object* v_repo_344_ = stack[0].m_obj;
lean_object* v_a_345_ = stack[1].m_obj;
lean_object* v_res_357_;
v_res_357_ = l_Lake_GitRepo_quietInit(v_repo_344_, v_a_345_);
stack->m_obj
 = v_res_357_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit___boxed(lean_object* v_repo_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lake_GitRepo_quietInit(v_repo_358_, v_a_359_);
return v_res_361_;
}
}
lean_object* l_Lake_GitRepo_bareInit(lean_object* v_repo_371_, lean_object* v_a_372_){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; uint8_t v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_374_ = ((lean_object*)(l_Lake_GitRepo_bareInit___closed__1));
v___x_375_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_376_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_377_, 0, v_repo_371_);
v___x_378_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_379_ = 1;
v___x_380_ = 0;
v___x_381_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_381_, 0, v___x_375_);
lean_ctor_set(v___x_381_, 1, v___x_376_);
lean_ctor_set(v___x_381_, 2, v___x_374_);
lean_ctor_set(v___x_381_, 3, v___x_377_);
lean_ctor_set(v___x_381_, 4, v___x_378_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*5, v___x_379_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*5 + 1, v___x_380_);
v___x_382_ = lean_box(0);
v___x_383_ = l_Lake_proc(v___x_381_, v___x_379_, v___x_382_, v_a_372_);
return v___x_383_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_bareInit_0interp(lean_interpreter_value* stack)
{
lean_object* v_repo_371_ = stack[0].m_obj;
lean_object* v_a_372_ = stack[1].m_obj;
lean_object* v_res_384_;
v_res_384_ = l_Lake_GitRepo_bareInit(v_repo_371_, v_a_372_);
stack->m_obj
 = v_res_384_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_bareInit___boxed(lean_object* v_repo_385_, lean_object* v_a_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lake_GitRepo_bareInit(v_repo_385_, v_a_386_);
return v_res_388_;
}
}
uint8_t l_Lake_GitRepo_insideWorkTree(lean_object* v_repo_397_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; uint8_t v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_399_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__2));
v___x_400_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_401_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_402_, 0, v_repo_397_);
v___x_403_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_404_ = 1;
v___x_405_ = 0;
v___x_406_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_406_, 0, v___x_400_);
lean_ctor_set(v___x_406_, 1, v___x_401_);
lean_ctor_set(v___x_406_, 2, v___x_399_);
lean_ctor_set(v___x_406_, 3, v___x_402_);
lean_ctor_set(v___x_406_, 4, v___x_403_);
lean_ctor_set_uint8(v___x_406_, sizeof(void*)*5, v___x_404_);
lean_ctor_set_uint8(v___x_406_, sizeof(void*)*5 + 1, v___x_405_);
v___x_407_ = l_Lake_testProc(v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_insideWorkTree_0interp(lean_interpreter_value* stack)
{
lean_object* v_repo_397_ = stack[0].m_obj;
uint8_t v_res_408_;
v_res_408_ = l_Lake_GitRepo_insideWorkTree(v_repo_397_);
stack->m_num = v_res_408_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_insideWorkTree___boxed(lean_object* v_repo_409_, lean_object* v_a_410_){
_start:
{
uint8_t v_res_411_; lean_object* v_r_412_; 
v_res_411_ = l_Lake_GitRepo_insideWorkTree(v_repo_409_);
v_r_412_ = lean_box(v_res_411_);
return v_r_412_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__3(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_416_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__0));
v___x_417_ = lean_unsigned_to_nat(4u);
v___x_418_ = lean_mk_empty_array_with_capacity(v___x_417_);
v___x_419_ = lean_array_push(v___x_418_, v___x_416_);
return v___x_419_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__4(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
v___x_421_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__3, &l_Lake_GitRepo_fetch___closed__3_once, _init_l_Lake_GitRepo_fetch___closed__3);
v___x_422_ = lean_array_push(v___x_421_, v___x_420_);
return v___x_422_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__5(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_423_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__2));
v___x_424_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__4, &l_Lake_GitRepo_fetch___closed__4_once, _init_l_Lake_GitRepo_fetch___closed__4);
v___x_425_ = lean_array_push(v___x_424_, v___x_423_);
return v___x_425_;
}
}
lean_object* l_Lake_GitRepo_fetch(lean_object* v_repo_426_, lean_object* v_remote_427_, lean_object* v_a_428_){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; uint8_t v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_430_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__5, &l_Lake_GitRepo_fetch___closed__5_once, _init_l_Lake_GitRepo_fetch___closed__5);
v___x_431_ = lean_array_push(v___x_430_, v_remote_427_);
v___x_432_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_433_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_434_, 0, v_repo_426_);
v___x_435_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_436_ = 1;
v___x_437_ = 0;
v___x_438_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_438_, 0, v___x_432_);
lean_ctor_set(v___x_438_, 1, v___x_433_);
lean_ctor_set(v___x_438_, 2, v___x_431_);
lean_ctor_set(v___x_438_, 3, v___x_434_);
lean_ctor_set(v___x_438_, 4, v___x_435_);
lean_ctor_set_uint8(v___x_438_, sizeof(void*)*5, v___x_436_);
lean_ctor_set_uint8(v___x_438_, sizeof(void*)*5 + 1, v___x_437_);
v___x_439_ = lean_box(0);
v___x_440_ = l_Lake_proc(v___x_438_, v___x_436_, v___x_439_, v_a_428_);
return v___x_440_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_fetch_0interp(lean_interpreter_value* stack)
{
lean_object* v_repo_426_ = stack[0].m_obj;
lean_object* v_remote_427_ = stack[1].m_obj;
lean_object* v_a_428_ = stack[2].m_obj;
lean_object* v_res_441_;
v_res_441_ = l_Lake_GitRepo_fetch(v_repo_426_, v_remote_427_, v_a_428_);
stack->m_obj
 = v_res_441_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch___boxed(lean_object* v_repo_442_, lean_object* v_remote_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lake_GitRepo_fetch(v_repo_442_, v_remote_443_, v_a_444_);
return v_res_446_;
}
}
static lean_object* _init_l_Lake_GitRepo_addWorktreeDetach___closed__3(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_450_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__0));
v___x_451_ = lean_unsigned_to_nat(5u);
v___x_452_ = lean_mk_empty_array_with_capacity(v___x_451_);
v___x_453_ = lean_array_push(v___x_452_, v___x_450_);
return v___x_453_;
}
}
static lean_object* _init_l_Lake_GitRepo_addWorktreeDetach___closed__4(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__1));
v___x_455_ = lean_obj_once(&l_Lake_GitRepo_addWorktreeDetach___closed__3, &l_Lake_GitRepo_addWorktreeDetach___closed__3_once, _init_l_Lake_GitRepo_addWorktreeDetach___closed__3);
v___x_456_ = lean_array_push(v___x_455_, v___x_454_);
return v___x_456_;
}
}
static lean_object* _init_l_Lake_GitRepo_addWorktreeDetach___closed__5(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__2));
v___x_458_ = lean_obj_once(&l_Lake_GitRepo_addWorktreeDetach___closed__4, &l_Lake_GitRepo_addWorktreeDetach___closed__4_once, _init_l_Lake_GitRepo_addWorktreeDetach___closed__4);
v___x_459_ = lean_array_push(v___x_458_, v___x_457_);
return v___x_459_;
}
}
lean_object* l_Lake_GitRepo_addWorktreeDetach(lean_object* v_path_460_, lean_object* v_rev_461_, lean_object* v_repo_462_, lean_object* v_a_463_){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; uint8_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_465_ = lean_obj_once(&l_Lake_GitRepo_addWorktreeDetach___closed__5, &l_Lake_GitRepo_addWorktreeDetach___closed__5_once, _init_l_Lake_GitRepo_addWorktreeDetach___closed__5);
v___x_466_ = lean_array_push(v___x_465_, v_path_460_);
v___x_467_ = lean_array_push(v___x_466_, v_rev_461_);
v___x_468_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_469_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_470_, 0, v_repo_462_);
v___x_471_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_472_ = 1;
v___x_473_ = 0;
v___x_474_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_474_, 0, v___x_468_);
lean_ctor_set(v___x_474_, 1, v___x_469_);
lean_ctor_set(v___x_474_, 2, v___x_467_);
lean_ctor_set(v___x_474_, 3, v___x_470_);
lean_ctor_set(v___x_474_, 4, v___x_471_);
lean_ctor_set_uint8(v___x_474_, sizeof(void*)*5, v___x_472_);
lean_ctor_set_uint8(v___x_474_, sizeof(void*)*5 + 1, v___x_473_);
v___x_475_ = lean_box(0);
v___x_476_ = l_Lake_proc(v___x_474_, v___x_472_, v___x_475_, v_a_463_);
return v___x_476_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_addWorktreeDetach_0interp(lean_interpreter_value* stack)
{
lean_object* v_path_460_ = stack[0].m_obj;
lean_object* v_rev_461_ = stack[1].m_obj;
lean_object* v_repo_462_ = stack[2].m_obj;
lean_object* v_a_463_ = stack[3].m_obj;
lean_object* v_res_477_;
v_res_477_ = l_Lake_GitRepo_addWorktreeDetach(v_path_460_, v_rev_461_, v_repo_462_, v_a_463_);
stack->m_obj
 = v_res_477_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_addWorktreeDetach___boxed(lean_object* v_path_478_, lean_object* v_rev_479_, lean_object* v_repo_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lake_GitRepo_addWorktreeDetach(v_path_478_, v_rev_479_, v_repo_480_, v_a_481_);
return v_res_483_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__2(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_486_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__0));
v___x_487_ = lean_unsigned_to_nat(3u);
v___x_488_ = lean_mk_empty_array_with_capacity(v___x_487_);
v___x_489_ = lean_array_push(v___x_488_, v___x_486_);
return v___x_489_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__3(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__1));
v___x_491_ = lean_obj_once(&l_Lake_GitRepo_checkoutBranch___closed__2, &l_Lake_GitRepo_checkoutBranch___closed__2_once, _init_l_Lake_GitRepo_checkoutBranch___closed__2);
v___x_492_ = lean_array_push(v___x_491_, v___x_490_);
return v___x_492_;
}
}
lean_object* l_Lake_GitRepo_checkoutBranch(lean_object* v_branch_493_, lean_object* v_repo_494_, lean_object* v_a_495_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; uint8_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_497_ = lean_obj_once(&l_Lake_GitRepo_checkoutBranch___closed__3, &l_Lake_GitRepo_checkoutBranch___closed__3_once, _init_l_Lake_GitRepo_checkoutBranch___closed__3);
v___x_498_ = lean_array_push(v___x_497_, v_branch_493_);
v___x_499_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_500_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_501_, 0, v_repo_494_);
v___x_502_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_503_ = 1;
v___x_504_ = 0;
v___x_505_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_505_, 0, v___x_499_);
lean_ctor_set(v___x_505_, 1, v___x_500_);
lean_ctor_set(v___x_505_, 2, v___x_498_);
lean_ctor_set(v___x_505_, 3, v___x_501_);
lean_ctor_set(v___x_505_, 4, v___x_502_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*5, v___x_503_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*5 + 1, v___x_504_);
v___x_506_ = lean_box(0);
v___x_507_ = l_Lake_proc(v___x_505_, v___x_503_, v___x_506_, v_a_495_);
return v___x_507_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_checkoutBranch_0interp(lean_interpreter_value* stack)
{
lean_object* v_branch_493_ = stack[0].m_obj;
lean_object* v_repo_494_ = stack[1].m_obj;
lean_object* v_a_495_ = stack[2].m_obj;
lean_object* v_res_508_;
v_res_508_ = l_Lake_GitRepo_checkoutBranch(v_branch_493_, v_repo_494_, v_a_495_);
stack->m_obj
 = v_res_508_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch___boxed(lean_object* v_branch_509_, lean_object* v_repo_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lake_GitRepo_checkoutBranch(v_branch_509_, v_repo_510_, v_a_511_);
return v_res_513_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__1(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_515_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__0));
v___x_516_ = lean_unsigned_to_nat(4u);
v___x_517_ = lean_mk_empty_array_with_capacity(v___x_516_);
v___x_518_ = lean_array_push(v___x_517_, v___x_515_);
return v___x_518_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__2(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_519_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__2));
v___x_520_ = lean_obj_once(&l_Lake_GitRepo_checkoutDetach___closed__1, &l_Lake_GitRepo_checkoutDetach___closed__1_once, _init_l_Lake_GitRepo_checkoutDetach___closed__1);
v___x_521_ = lean_array_push(v___x_520_, v___x_519_);
return v___x_521_;
}
}
lean_object* l_Lake_GitRepo_checkoutDetach(lean_object* v_hash_522_, lean_object* v_repo_523_, lean_object* v_a_524_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; uint8_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_526_ = ((lean_object*)(l_Lake_GitRepo_checkoutDetach___closed__0));
v___x_527_ = lean_obj_once(&l_Lake_GitRepo_checkoutDetach___closed__2, &l_Lake_GitRepo_checkoutDetach___closed__2_once, _init_l_Lake_GitRepo_checkoutDetach___closed__2);
v___x_528_ = lean_array_push(v___x_527_, v_hash_522_);
v___x_529_ = lean_array_push(v___x_528_, v___x_526_);
v___x_530_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_531_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_532_, 0, v_repo_523_);
v___x_533_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_534_ = 1;
v___x_535_ = 0;
v___x_536_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_536_, 0, v___x_530_);
lean_ctor_set(v___x_536_, 1, v___x_531_);
lean_ctor_set(v___x_536_, 2, v___x_529_);
lean_ctor_set(v___x_536_, 3, v___x_532_);
lean_ctor_set(v___x_536_, 4, v___x_533_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*5, v___x_534_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*5 + 1, v___x_535_);
v___x_537_ = lean_box(0);
v___x_538_ = l_Lake_proc(v___x_536_, v___x_534_, v___x_537_, v_a_524_);
return v___x_538_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_checkoutDetach_0interp(lean_interpreter_value* stack)
{
lean_object* v_hash_522_ = stack[0].m_obj;
lean_object* v_repo_523_ = stack[1].m_obj;
lean_object* v_a_524_ = stack[2].m_obj;
lean_object* v_res_539_;
v_res_539_ = l_Lake_GitRepo_checkoutDetach(v_hash_522_, v_repo_523_, v_a_524_);
stack->m_obj
 = v_res_539_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach___boxed(lean_object* v_hash_540_, lean_object* v_repo_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lake_GitRepo_checkoutDetach(v_hash_540_, v_repo_541_, v_a_542_);
return v_res_544_;
}
}
lean_object* l_Lake_GitRepo_gcAuto(lean_object* v_repo_553_, lean_object* v_a_554_){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; uint8_t v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_556_ = ((lean_object*)(l_Lake_GitRepo_gcAuto___closed__2));
v___x_557_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_558_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v_repo_553_);
v___x_560_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_561_ = 1;
v___x_562_ = 0;
v___x_563_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_563_, 0, v___x_557_);
lean_ctor_set(v___x_563_, 1, v___x_558_);
lean_ctor_set(v___x_563_, 2, v___x_556_);
lean_ctor_set(v___x_563_, 3, v___x_559_);
lean_ctor_set(v___x_563_, 4, v___x_560_);
lean_ctor_set_uint8(v___x_563_, sizeof(void*)*5, v___x_561_);
lean_ctor_set_uint8(v___x_563_, sizeof(void*)*5 + 1, v___x_562_);
v___x_564_ = lean_box(0);
v___x_565_ = l_Lake_proc(v___x_563_, v___x_561_, v___x_564_, v_a_554_);
return v___x_565_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_gcAuto_0interp(lean_interpreter_value* stack)
{
lean_object* v_repo_553_ = stack[0].m_obj;
lean_object* v_a_554_ = stack[1].m_obj;
lean_object* v_res_566_;
v_res_566_ = l_Lake_GitRepo_gcAuto(v_repo_553_, v_a_554_);
stack->m_obj
 = v_res_566_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_gcAuto___boxed(lean_object* v_repo_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lake_GitRepo_gcAuto(v_repo_567_, v_a_568_);
return v_res_570_;
}
}
lean_object* l_Lake_GitRepo_clean(lean_object* v_repo_579_, lean_object* v_a_580_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; uint8_t v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_582_ = ((lean_object*)(l_Lake_GitRepo_clean___closed__2));
v___x_583_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_584_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_585_, 0, v_repo_579_);
v___x_586_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_587_ = 1;
v___x_588_ = 0;
v___x_589_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_589_, 0, v___x_583_);
lean_ctor_set(v___x_589_, 1, v___x_584_);
lean_ctor_set(v___x_589_, 2, v___x_582_);
lean_ctor_set(v___x_589_, 3, v___x_585_);
lean_ctor_set(v___x_589_, 4, v___x_586_);
lean_ctor_set_uint8(v___x_589_, sizeof(void*)*5, v___x_587_);
lean_ctor_set_uint8(v___x_589_, sizeof(void*)*5 + 1, v___x_588_);
v___x_590_ = lean_box(0);
v___x_591_ = l_Lake_proc(v___x_589_, v___x_587_, v___x_590_, v_a_580_);
return v___x_591_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_clean_0interp(lean_interpreter_value* stack)
{
lean_object* v_repo_579_ = stack[0].m_obj;
lean_object* v_a_580_ = stack[1].m_obj;
lean_object* v_res_592_;
v_res_592_ = l_Lake_GitRepo_clean(v_repo_579_, v_a_580_);
stack->m_obj
 = v_res_592_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean___boxed(lean_object* v_repo_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lake_GitRepo_clean(v_repo_593_, v_a_594_);
return v_res_596_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_599_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__0));
v___x_600_ = lean_unsigned_to_nat(4u);
v___x_601_ = lean_mk_empty_array_with_capacity(v___x_600_);
v___x_602_ = lean_array_push(v___x_601_, v___x_599_);
return v___x_602_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_603_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_604_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__2, &l_Lake_GitRepo_resolveRevision_x3f___closed__2_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2);
v___x_605_ = lean_array_push(v___x_604_, v___x_603_);
return v___x_605_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_606_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__1));
v___x_607_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__3, &l_Lake_GitRepo_resolveRevision_x3f___closed__3_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3);
v___x_608_ = lean_array_push(v___x_607_, v___x_606_);
return v___x_608_;
}
}
lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object* v_rev_609_, lean_object* v_repo_610_){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; uint8_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_612_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__4, &l_Lake_GitRepo_resolveRevision_x3f___closed__4_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4);
v___x_613_ = lean_array_push(v___x_612_, v_rev_609_);
v___x_614_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_615_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_616_, 0, v_repo_610_);
v___x_617_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_618_ = 1;
v___x_619_ = 0;
v___x_620_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_620_, 0, v___x_614_);
lean_ctor_set(v___x_620_, 1, v___x_615_);
lean_ctor_set(v___x_620_, 2, v___x_613_);
lean_ctor_set(v___x_620_, 3, v___x_616_);
lean_ctor_set(v___x_620_, 4, v___x_617_);
lean_ctor_set_uint8(v___x_620_, sizeof(void*)*5, v___x_618_);
lean_ctor_set_uint8(v___x_620_, sizeof(void*)*5 + 1, v___x_619_);
v___x_621_ = l_Lake_captureProc_x3f(v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_resolveRevision_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_rev_609_ = stack[0].m_obj;
lean_object* v_repo_610_ = stack[1].m_obj;
lean_object* v_res_622_;
v_res_622_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_609_, v_repo_610_);
stack->m_obj
 = v_res_622_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f___boxed(lean_object* v_rev_623_, lean_object* v_repo_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_623_, v_repo_624_);
return v_res_626_;
}
}
lean_object* l_Lake_GitRepo_findCommit_x3f(lean_object* v_rev_628_, lean_object* v_repo_629_){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v___x_639_; uint8_t v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_631_ = ((lean_object*)(l_Lake_GitRepo_findCommit_x3f___closed__0));
v___x_632_ = lean_string_append(v_rev_628_, v___x_631_);
v___x_633_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__4, &l_Lake_GitRepo_resolveRevision_x3f___closed__4_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4);
v___x_634_ = lean_array_push(v___x_633_, v___x_632_);
v___x_635_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_636_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_637_, 0, v_repo_629_);
v___x_638_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_639_ = 1;
v___x_640_ = 0;
v___x_641_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_641_, 0, v___x_635_);
lean_ctor_set(v___x_641_, 1, v___x_636_);
lean_ctor_set(v___x_641_, 2, v___x_634_);
lean_ctor_set(v___x_641_, 3, v___x_637_);
lean_ctor_set(v___x_641_, 4, v___x_638_);
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*5, v___x_639_);
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*5 + 1, v___x_640_);
v___x_642_ = l_Lake_captureProc_x3f(v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_findCommit_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_rev_628_ = stack[0].m_obj;
lean_object* v_repo_629_ = stack[1].m_obj;
lean_object* v_res_643_;
v_res_643_ = l_Lake_GitRepo_findCommit_x3f(v_rev_628_, v_repo_629_);
stack->m_obj
 = v_res_643_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findCommit_x3f___boxed(lean_object* v_rev_644_, lean_object* v_repo_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lake_GitRepo_findCommit_x3f(v_rev_644_, v_repo_645_);
return v_res_647_;
}
}
lean_object* l_Lake_GitRepo_resolveRevision(lean_object* v_rev_650_, lean_object* v_repo_651_, lean_object* v_a_652_){
_start:
{
uint8_t v___x_654_; 
v___x_654_ = l_Lake_GitRev_isFullSha1(v_rev_650_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
lean_inc_ref(v_repo_651_);
lean_inc_ref(v_rev_650_);
v___x_655_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_650_, v_repo_651_);
if (lean_obj_tag(v___x_655_) == 1)
{
lean_object* v_val_656_; lean_object* v___x_657_; 
lean_dec_ref(v_repo_651_);
lean_dec_ref(v_rev_650_);
v_val_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_val_656_);
lean_dec_ref_known(v___x_655_, 1);
v___x_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_657_, 0, v_val_656_);
lean_ctor_set(v___x_657_, 1, v_a_652_);
return v___x_657_;
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
lean_dec(v___x_655_);
v___x_658_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__0));
v___x_659_ = lean_string_append(v_repo_651_, v___x_658_);
v___x_660_ = lean_string_append(v___x_659_, v_rev_650_);
lean_dec_ref(v_rev_650_);
v___x_661_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__1));
v___x_662_ = lean_string_append(v___x_660_, v___x_661_);
v___x_663_ = 3;
v___x_664_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_664_, 0, v___x_662_);
lean_ctor_set_uint8(v___x_664_, sizeof(void*)*1, v___x_663_);
v___x_665_ = lean_array_get_size(v_a_652_);
v___x_666_ = lean_array_push(v_a_652_, v___x_664_);
v___x_667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
return v___x_667_;
}
}
else
{
lean_object* v___x_668_; 
lean_dec_ref(v_repo_651_);
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v_rev_650_);
lean_ctor_set(v___x_668_, 1, v_a_652_);
return v___x_668_;
}
}
}
LEAN_EXPORT void l_Lake_GitRepo_resolveRevision_0interp(lean_interpreter_value* stack)
{
lean_object* v_rev_650_ = stack[0].m_obj;
lean_object* v_repo_651_ = stack[1].m_obj;
lean_object* v_a_652_ = stack[2].m_obj;
lean_object* v_res_669_;
v_res_669_ = l_Lake_GitRepo_resolveRevision(v_rev_650_, v_repo_651_, v_a_652_);
stack->m_obj
 = v_res_669_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision___boxed(lean_object* v_rev_670_, lean_object* v_repo_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lake_GitRepo_resolveRevision(v_rev_670_, v_repo_671_, v_a_672_);
return v_res_674_;
}
}
lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object* v_repo_675_){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = ((lean_object*)(l_Lake_GitRev_head___closed__0));
v___x_678_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_677_, v_repo_675_);
return v___x_678_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_getHeadRevision_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_repo_675_ = stack[0].m_obj;
lean_object* v_res_679_;
v_res_679_ = l_Lake_GitRepo_getHeadRevision_x3f(v_repo_675_);
stack->m_obj
 = v_res_679_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f___boxed(lean_object* v_repo_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lake_GitRepo_getHeadRevision_x3f(v_repo_680_);
return v_res_682_;
}
}
lean_object* l_Lake_GitRepo_getHeadRevision(lean_object* v_repo_684_, lean_object* v_a_685_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = ((lean_object*)(l_Lake_GitRev_head___closed__0));
lean_inc_ref(v_repo_684_);
v___x_688_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_687_, v_repo_684_);
if (lean_obj_tag(v___x_688_) == 1)
{
lean_object* v_val_689_; lean_object* v___x_690_; 
lean_dec_ref(v_repo_684_);
v_val_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_val_689_);
lean_dec_ref_known(v___x_688_, 1);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v_val_689_);
lean_ctor_set(v___x_690_, 1, v_a_685_);
return v___x_690_;
}
else
{
lean_object* v___x_691_; lean_object* v___x_692_; uint8_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
lean_dec(v___x_688_);
v___x_691_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevision___closed__0));
v___x_692_ = lean_string_append(v_repo_684_, v___x_691_);
v___x_693_ = 3;
v___x_694_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set_uint8(v___x_694_, sizeof(void*)*1, v___x_693_);
v___x_695_ = lean_array_get_size(v_a_685_);
v___x_696_ = lean_array_push(v_a_685_, v___x_694_);
v___x_697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_695_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
return v___x_697_;
}
}
}
LEAN_EXPORT void l_Lake_GitRepo_getHeadRevision_0interp(lean_interpreter_value* stack)
{
lean_object* v_repo_684_ = stack[0].m_obj;
lean_object* v_a_685_ = stack[1].m_obj;
lean_object* v_res_698_;
v_res_698_ = l_Lake_GitRepo_getHeadRevision(v_repo_684_, v_a_685_);
stack->m_obj
 = v_res_698_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision___boxed(lean_object* v_repo_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lake_GitRepo_getHeadRevision(v_repo_699_, v_a_700_);
return v_res_702_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetchRevision_x3f___closed__1(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_704_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__0));
v___x_705_ = lean_unsigned_to_nat(6u);
v___x_706_ = lean_mk_empty_array_with_capacity(v___x_705_);
v___x_707_ = lean_array_push(v___x_706_, v___x_704_);
return v___x_707_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetchRevision_x3f___closed__2(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_708_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
v___x_709_ = lean_obj_once(&l_Lake_GitRepo_fetchRevision_x3f___closed__1, &l_Lake_GitRepo_fetchRevision_x3f___closed__1_once, _init_l_Lake_GitRepo_fetchRevision_x3f___closed__1);
v___x_710_ = lean_array_push(v___x_709_, v___x_708_);
return v___x_710_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetchRevision_x3f___closed__3(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_711_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__2));
v___x_712_ = lean_obj_once(&l_Lake_GitRepo_fetchRevision_x3f___closed__2, &l_Lake_GitRepo_fetchRevision_x3f___closed__2_once, _init_l_Lake_GitRepo_fetchRevision_x3f___closed__2);
v___x_713_ = lean_array_push(v___x_712_, v___x_711_);
return v___x_713_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetchRevision_x3f___closed__4(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_714_ = ((lean_object*)(l_Lake_GitRepo_fetchRevision_x3f___closed__0));
v___x_715_ = lean_obj_once(&l_Lake_GitRepo_fetchRevision_x3f___closed__3, &l_Lake_GitRepo_fetchRevision_x3f___closed__3_once, _init_l_Lake_GitRepo_fetchRevision_x3f___closed__3);
v___x_716_ = lean_array_push(v___x_715_, v___x_714_);
return v___x_716_;
}
}
lean_object* l_Lake_GitRepo_fetchRevision_x3f(lean_object* v_repo_718_, lean_object* v_remote_719_, lean_object* v_rev_720_, lean_object* v_a_721_){
_start:
{
lean_object* v_a_724_; lean_object* v_a_725_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v_args_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; uint8_t v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_727_ = lean_obj_once(&l_Lake_GitRepo_fetchRevision_x3f___closed__4, &l_Lake_GitRepo_fetchRevision_x3f___closed__4_once, _init_l_Lake_GitRepo_fetchRevision_x3f___closed__4);
v___x_728_ = lean_array_push(v___x_727_, v_remote_719_);
v_args_729_ = lean_array_push(v___x_728_, v_rev_720_);
v___x_730_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_731_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
lean_inc_ref(v_repo_718_);
v___x_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_732_, 0, v_repo_718_);
v___x_733_ = lean_unsigned_to_nat(0u);
v___x_734_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_735_ = 1;
v___x_736_ = 0;
v___x_737_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_737_, 0, v___x_730_);
lean_ctor_set(v___x_737_, 1, v___x_731_);
lean_ctor_set(v___x_737_, 2, v_args_729_);
lean_ctor_set(v___x_737_, 3, v___x_732_);
lean_ctor_set(v___x_737_, 4, v___x_734_);
lean_ctor_set_uint8(v___x_737_, sizeof(void*)*5, v___x_735_);
lean_ctor_set_uint8(v___x_737_, sizeof(void*)*5 + 1, v___x_736_);
v___x_738_ = lean_box(0);
v___x_739_ = lean_array_get_size(v_a_721_);
lean_inc_ref(v___x_737_);
v___x_740_ = l_Lake_mkCmdLog(v___x_737_);
v___x_741_ = 0;
v___x_742_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set_uint8(v___x_742_, sizeof(void*)*1, v___x_741_);
v___x_743_ = lean_array_push(v_a_721_, v___x_742_);
v___x_744_ = l_IO_Process_output(v___x_737_, v___x_738_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; uint32_t v_exitCode_746_; lean_object* v_stdout_747_; lean_object* v_stderr_748_; uint32_t v___x_749_; uint8_t v___x_750_; lean_object* v___y_752_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___y_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v___x_744_, 1);
v_exitCode_746_ = lean_ctor_get_uint32(v_a_745_, sizeof(void*)*2);
v_stdout_747_ = lean_ctor_get(v_a_745_, 0);
lean_inc_ref(v_stdout_747_);
v_stderr_748_ = lean_ctor_get(v_a_745_, 1);
lean_inc_ref(v_stderr_748_);
lean_dec(v_a_745_);
v___x_749_ = 0;
v___x_750_ = lean_uint32_dec_eq(v_exitCode_746_, v___x_749_);
v___x_784_ = lean_box(v___x_750_);
v___x_785_ = lean_box(v___x_741_);
v___y_786_ = lean_alloc_closure((void*)(l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0___boxed), 5, 2);
lean_closure_set(v___y_786_, 0, v___x_784_);
lean_closure_set(v___y_786_, 1, v___x_785_);
v___x_787_ = lean_string_utf8_byte_size(v_stdout_747_);
v___x_788_ = lean_nat_dec_eq(v___x_787_, v___x_733_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v_a_795_; lean_object* v_a_796_; lean_object* v___x_797_; 
v___x_789_ = ((lean_object*)(l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__0));
v___x_790_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_790_, 0, v_stdout_747_);
lean_ctor_set(v___x_790_, 1, v___x_733_);
lean_ctor_set(v___x_790_, 2, v___x_787_);
v___x_791_ = l_String_Slice_trimAscii(v___x_790_);
v___x_792_ = l_String_Slice_toString(v___x_791_);
lean_dec_ref(v___x_791_);
v___x_793_ = lean_string_append(v___x_789_, v___x_792_);
lean_dec_ref(v___x_792_);
v___x_794_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0(v___x_750_, v___x_741_, v___x_793_, v___x_743_);
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
v_a_796_ = lean_ctor_get(v___x_794_, 1);
lean_inc(v_a_796_);
lean_dec_ref(v___x_794_);
v___x_797_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1(v_stderr_748_, v___x_733_, v___y_786_, v_a_795_, v_a_796_);
v___y_752_ = v___x_797_;
goto v___jp_751_;
}
else
{
lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec_ref(v_stdout_747_);
v___x_798_ = lean_box(0);
v___x_799_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1(v_stderr_748_, v___x_733_, v___y_786_, v___x_798_, v___x_743_);
v___y_752_ = v___x_799_;
goto v___jp_751_;
}
v___jp_751_:
{
if (lean_obj_tag(v___y_752_) == 0)
{
if (v___x_750_ == 0)
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec_ref(v_repo_718_);
v_a_753_ = lean_ctor_get(v___y_752_, 1);
v_isSharedCheck_760_ = !lean_is_exclusive(v___y_752_);
if (v_isSharedCheck_760_ == 0)
{
lean_object* v_unused_761_; 
v_unused_761_ = lean_ctor_get(v___y_752_, 0);
lean_dec(v_unused_761_);
v___x_755_ = v___y_752_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___y_752_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v___x_738_);
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_780_; 
v_a_762_ = lean_ctor_get(v___y_752_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v___y_752_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v___y_752_, 0);
lean_dec(v_unused_781_);
v___x_764_ = v___y_752_;
v_isShared_765_ = v_isSharedCheck_780_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___y_752_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_780_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = ((lean_object*)(l_Lake_GitRev_fetchHead___closed__0));
lean_inc_ref(v_repo_718_);
v___x_767_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_766_, v_repo_718_);
if (lean_obj_tag(v___x_767_) == 1)
{
lean_object* v___x_769_; 
lean_dec_ref(v_repo_718_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_767_);
v___x_769_ = v___x_764_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_a_762_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
lean_dec(v___x_767_);
v___x_771_ = ((lean_object*)(l_Lake_GitRepo_fetchRevision_x3f___closed__5));
v___x_772_ = lean_string_append(v_repo_718_, v___x_771_);
v___x_773_ = 3;
v___x_774_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_774_, 0, v___x_772_);
lean_ctor_set_uint8(v___x_774_, sizeof(void*)*1, v___x_773_);
v___x_775_ = lean_array_get_size(v_a_762_);
v___x_776_ = lean_array_push(v_a_762_, v___x_774_);
if (v_isShared_765_ == 0)
{
lean_ctor_set_tag(v___x_764_, 1);
lean_ctor_set(v___x_764_, 1, v___x_776_);
lean_ctor_set(v___x_764_, 0, v___x_775_);
v___x_778_ = v___x_764_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
else
{
lean_object* v_a_782_; lean_object* v_a_783_; 
lean_dec_ref(v_repo_718_);
v_a_782_ = lean_ctor_get(v___y_752_, 0);
lean_inc(v_a_782_);
v_a_783_ = lean_ctor_get(v___y_752_, 1);
lean_inc(v_a_783_);
lean_dec_ref_known(v___y_752_, 2);
v_a_724_ = v_a_782_;
v_a_725_ = v_a_783_;
goto v___jp_723_;
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec_ref(v_repo_718_);
v_a_800_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_744_, 1);
v___x_801_ = ((lean_object*)(l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__1));
v___x_802_ = lean_io_error_to_string(v_a_800_);
v___x_803_ = lean_string_append(v___x_801_, v___x_802_);
lean_dec_ref(v___x_802_);
v___x_804_ = 3;
v___x_805_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_805_, 0, v___x_803_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*1, v___x_804_);
v___x_806_ = lean_array_push(v___x_743_, v___x_805_);
v_a_724_ = v___x_739_;
v_a_725_ = v___x_806_;
goto v___jp_723_;
}
v___jp_723_:
{
lean_object* v___x_726_; 
v___x_726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_726_, 0, v_a_724_);
lean_ctor_set(v___x_726_, 1, v_a_725_);
return v___x_726_;
}
}
}
LEAN_EXPORT void l_Lake_GitRepo_fetchRevision_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_repo_718_ = stack[0].m_obj;
lean_object* v_remote_719_ = stack[1].m_obj;
lean_object* v_rev_720_ = stack[2].m_obj;
lean_object* v_a_721_ = stack[3].m_obj;
lean_object* v_res_807_;
v_res_807_ = l_Lake_GitRepo_fetchRevision_x3f(v_repo_718_, v_remote_719_, v_rev_720_, v_a_721_);
stack->m_obj
 = v_res_807_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetchRevision_x3f___boxed(lean_object* v_repo_808_, lean_object* v_remote_809_, lean_object* v_rev_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lake_GitRepo_fetchRevision_x3f(v_repo_808_, v_remote_809_, v_rev_810_, v_a_811_);
return v_res_813_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___redArg(){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___redArg___closed__0));
return v___x_817_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_818_;
v_res_818_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___redArg();
stack->m_obj
 = v_res_818_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___redArg___boxed(lean_object* v___dummy_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___redArg();
return v_res_820_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0(void){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___redArg();
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(lean_object* v_s_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___boxed(lean_object* v_s_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v_s_824_);
lean_dec_ref(v_s_824_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(lean_object* v___x_826_, lean_object* v___x_827_, lean_object* v___x_828_, lean_object* v_a_829_, lean_object* v_b_830_){
_start:
{
lean_object* v_it_832_; lean_object* v_startInclusive_833_; lean_object* v_endExclusive_834_; 
if (lean_obj_tag(v_a_829_) == 0)
{
lean_object* v_currPos_839_; lean_object* v_searcher_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_863_; 
v_currPos_839_ = lean_ctor_get(v_a_829_, 0);
v_searcher_840_ = lean_ctor_get(v_a_829_, 1);
v_isSharedCheck_863_ = !lean_is_exclusive(v_a_829_);
if (v_isSharedCheck_863_ == 0)
{
v___x_842_ = v_a_829_;
v_isShared_843_ = v_isSharedCheck_863_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_searcher_840_);
lean_inc(v_currPos_839_);
lean_dec(v_a_829_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_863_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
uint8_t v_decide_844_; 
v_decide_844_ = lean_nat_dec_eq(v_searcher_840_, v___x_828_);
if (v_decide_844_ == 0)
{
uint32_t v___x_845_; uint32_t v___x_846_; uint8_t v___x_847_; 
v___x_845_ = 10;
v___x_846_ = lean_string_utf8_get_fast(v___x_826_, v_searcher_840_);
v___x_847_ = lean_uint32_dec_eq(v___x_846_, v___x_845_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_848_ = lean_string_utf8_next_fast(v___x_826_, v_searcher_840_);
lean_dec(v_searcher_840_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v___x_848_);
v___x_850_ = v___x_842_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_currPos_839_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v___x_848_);
v___x_850_ = v_reuseFailAlloc_852_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
v_a_829_ = v___x_850_;
goto _start;
}
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v_slice_856_; lean_object* v_nextIt_858_; 
v___x_853_ = lean_string_utf8_next_fast(v___x_826_, v_searcher_840_);
v___x_854_ = lean_nat_sub(v___x_853_, v_searcher_840_);
v___x_855_ = lean_nat_add(v_searcher_840_, v___x_854_);
lean_dec(v___x_854_);
v_slice_856_ = l_String_Slice_subslice_x21(v___x_827_, v_currPos_839_, v_searcher_840_);
lean_inc(v___x_855_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v___x_855_);
lean_ctor_set(v___x_842_, 0, v___x_855_);
v_nextIt_858_ = v___x_842_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v___x_855_);
v_nextIt_858_ = v_reuseFailAlloc_861_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v_startInclusive_859_; lean_object* v_endExclusive_860_; 
v_startInclusive_859_ = lean_ctor_get(v_slice_856_, 0);
lean_inc(v_startInclusive_859_);
v_endExclusive_860_ = lean_ctor_get(v_slice_856_, 1);
lean_inc(v_endExclusive_860_);
lean_dec_ref(v_slice_856_);
v_it_832_ = v_nextIt_858_;
v_startInclusive_833_ = v_startInclusive_859_;
v_endExclusive_834_ = v_endExclusive_860_;
goto v___jp_831_;
}
}
}
else
{
lean_object* v___x_862_; 
lean_del_object(v___x_842_);
lean_dec(v_searcher_840_);
v___x_862_ = lean_box(1);
lean_inc(v___x_828_);
v_it_832_ = v___x_862_;
v_startInclusive_833_ = v_currPos_839_;
v_endExclusive_834_ = v___x_828_;
goto v___jp_831_;
}
}
}
else
{
lean_dec(v___x_828_);
lean_dec_ref(v___x_826_);
return v_b_830_;
}
v___jp_831_:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
lean_inc_ref(v___x_826_);
v___x_835_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_835_, 0, v___x_826_);
lean_ctor_set(v___x_835_, 1, v_startInclusive_833_);
lean_ctor_set(v___x_835_, 2, v_endExclusive_834_);
v___x_836_ = l_String_Slice_toString(v___x_835_);
lean_dec_ref_known(v___x_835_, 3);
v___x_837_ = lean_array_push(v_b_830_, v___x_836_);
v_a_829_ = v_it_832_;
v_b_830_ = v___x_837_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___boxed(lean_object* v___x_864_, lean_object* v___x_865_, lean_object* v___x_866_, lean_object* v_a_867_, lean_object* v_b_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_864_, v___x_865_, v___x_866_, v_a_867_, v_b_868_);
lean_dec_ref(v___x_865_);
return v_res_869_;
}
}
static lean_object* _init_l_Lake_GitRepo_getHeadRevisions___closed__3(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_878_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevisions___closed__2));
v___x_879_ = lean_unsigned_to_nat(2u);
v___x_880_ = lean_mk_empty_array_with_capacity(v___x_879_);
v___x_881_ = lean_array_push(v___x_880_, v___x_878_);
return v___x_881_;
}
}
lean_object* l_Lake_GitRepo_getHeadRevisions(lean_object* v_repo_882_, lean_object* v_n_883_, lean_object* v_a_884_){
_start:
{
lean_object* v___y_887_; lean_object* v_args_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v_args_933_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevisions___closed__1));
v___x_934_ = lean_unsigned_to_nat(0u);
v___x_935_ = lean_nat_dec_eq(v_n_883_, v___x_934_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_936_ = l_Nat_reprFast(v_n_883_);
v___x_937_ = lean_obj_once(&l_Lake_GitRepo_getHeadRevisions___closed__3, &l_Lake_GitRepo_getHeadRevisions___closed__3_once, _init_l_Lake_GitRepo_getHeadRevisions___closed__3);
v___x_938_ = lean_array_push(v___x_937_, v___x_936_);
v___x_939_ = l_Array_append___redArg(v_args_933_, v___x_938_);
lean_dec_ref(v___x_938_);
v___y_887_ = v___x_939_;
goto v___jp_886_;
}
else
{
lean_dec(v_n_883_);
v___y_887_ = v_args_933_;
goto v___jp_886_;
}
v___jp_886_:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; uint8_t v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_888_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_889_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_890_, 0, v_repo_882_);
v___x_891_ = lean_unsigned_to_nat(0u);
v___x_892_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_893_ = 1;
v___x_894_ = 0;
v___x_895_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_895_, 0, v___x_888_);
lean_ctor_set(v___x_895_, 1, v___x_889_);
lean_ctor_set(v___x_895_, 2, v___y_887_);
lean_ctor_set(v___x_895_, 3, v___x_890_);
lean_ctor_set(v___x_895_, 4, v___x_892_);
lean_ctor_set_uint8(v___x_895_, sizeof(void*)*5, v___x_893_);
lean_ctor_set_uint8(v___x_895_, sizeof(void*)*5 + 1, v___x_894_);
v___x_896_ = l_Lake_captureProc_x27(v___x_895_, v_a_884_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_923_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
v_a_898_ = lean_ctor_get(v___x_896_, 1);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_923_ == 0)
{
v___x_900_ = v___x_896_;
v_isShared_901_ = v_isSharedCheck_923_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_923_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v_stdout_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v_str_906_; lean_object* v_startInclusive_907_; lean_object* v_endExclusive_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_922_; 
v_stdout_902_ = lean_ctor_get(v_a_897_, 0);
lean_inc_ref(v_stdout_902_);
lean_dec(v_a_897_);
v___x_903_ = lean_string_utf8_byte_size(v_stdout_902_);
v___x_904_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_904_, 0, v_stdout_902_);
lean_ctor_set(v___x_904_, 1, v___x_891_);
lean_ctor_set(v___x_904_, 2, v___x_903_);
v___x_905_ = l_String_Slice_trimAscii(v___x_904_);
v_str_906_ = lean_ctor_get(v___x_905_, 0);
v_startInclusive_907_ = lean_ctor_get(v___x_905_, 1);
v_endExclusive_908_ = lean_ctor_get(v___x_905_, 2);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_922_ == 0)
{
v___x_910_ = v___x_905_;
v_isShared_911_ = v_isSharedCheck_922_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_endExclusive_908_);
lean_inc(v_startInclusive_907_);
lean_inc(v_str_906_);
lean_dec(v___x_905_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_922_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_915_; 
v___x_912_ = lean_string_utf8_extract_fast(v_str_906_, v_startInclusive_907_, v_endExclusive_908_);
lean_dec(v_endExclusive_908_);
lean_dec(v_startInclusive_907_);
lean_dec_ref(v_str_906_);
v___x_913_ = lean_string_utf8_byte_size(v___x_912_);
lean_inc_ref(v___x_912_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 2, v___x_913_);
lean_ctor_set(v___x_910_, 1, v___x_891_);
lean_ctor_set(v___x_910_, 0, v___x_912_);
v___x_915_ = v___x_910_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v___x_913_);
v___x_915_ = v_reuseFailAlloc_921_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_916_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0);
v___x_917_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_912_, v___x_915_, v___x_913_, v___x_916_, v___x_892_);
lean_dec_ref(v___x_915_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_917_);
v___x_919_ = v___x_900_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_a_898_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
}
else
{
lean_object* v_a_924_; lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
v_a_924_ = lean_ctor_get(v___x_896_, 0);
v_a_925_ = lean_ctor_get(v___x_896_, 1);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_896_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_inc(v_a_924_);
lean_dec(v___x_896_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_924_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_GitRepo_getHeadRevisions_0interp(lean_interpreter_value* stack)
{
lean_object* v_repo_882_ = stack[0].m_obj;
lean_object* v_n_883_ = stack[1].m_obj;
lean_object* v_a_884_ = stack[2].m_obj;
lean_object* v_res_940_;
v_res_940_ = l_Lake_GitRepo_getHeadRevisions(v_repo_882_, v_n_883_, v_a_884_);
stack->m_obj
 = v_res_940_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions___boxed(lean_object* v_repo_941_, lean_object* v_n_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lake_GitRepo_getHeadRevisions(v_repo_941_, v_n_942_, v_a_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(lean_object* v___x_946_, lean_object* v___x_947_, lean_object* v___x_948_, lean_object* v_inst_949_, lean_object* v_R_950_, lean_object* v_a_951_, lean_object* v_b_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_946_, v___x_947_, v___x_948_, v_a_951_, v_b_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___boxed(lean_object* v___x_954_, lean_object* v___x_955_, lean_object* v___x_956_, lean_object* v_inst_957_, lean_object* v_R_958_, lean_object* v_a_959_, lean_object* v_b_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(v___x_954_, v___x_955_, v___x_956_, v_inst_957_, v_R_958_, v_a_959_, v_b_960_);
lean_dec_ref(v___x_955_);
return v_res_961_;
}
}
lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object* v_rev_962_, lean_object* v_remote_963_, lean_object* v_repo_964_, lean_object* v_a_965_){
_start:
{
lean_object* v_rev_968_; lean_object* v___y_969_; uint8_t v___x_971_; 
v___x_971_ = l_Lake_GitRev_isFullSha1(v_rev_962_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_972_ = ((lean_object*)(l_Lake_GitRev_withRemote___closed__0));
v___x_973_ = lean_string_append(v_remote_963_, v___x_972_);
v___x_974_ = lean_string_append(v___x_973_, v_rev_962_);
lean_inc_ref(v_repo_964_);
v___x_975_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_974_, v_repo_964_);
if (lean_obj_tag(v___x_975_) == 1)
{
lean_object* v_val_976_; 
lean_dec_ref(v_repo_964_);
lean_dec_ref(v_rev_962_);
v_val_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_val_976_);
lean_dec_ref_known(v___x_975_, 1);
v_rev_968_ = v_val_976_;
v___y_969_ = v_a_965_;
goto v___jp_967_;
}
else
{
lean_object* v___x_977_; 
lean_dec(v___x_975_);
lean_inc_ref(v_repo_964_);
lean_inc_ref(v_rev_962_);
v___x_977_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_962_, v_repo_964_);
if (lean_obj_tag(v___x_977_) == 1)
{
lean_object* v_val_978_; 
lean_dec_ref(v_repo_964_);
lean_dec_ref(v_rev_962_);
v_val_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_val_978_);
lean_dec_ref_known(v___x_977_, 1);
v_rev_968_ = v_val_978_;
v___y_969_ = v_a_965_;
goto v___jp_967_;
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
lean_dec(v___x_977_);
v___x_979_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__0));
v___x_980_ = lean_string_append(v_repo_964_, v___x_979_);
v___x_981_ = lean_string_append(v___x_980_, v_rev_962_);
lean_dec_ref(v_rev_962_);
v___x_982_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__1));
v___x_983_ = lean_string_append(v___x_981_, v___x_982_);
v___x_984_ = 3;
v___x_985_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*1, v___x_984_);
v___x_986_ = lean_array_get_size(v_a_965_);
v___x_987_ = lean_array_push(v_a_965_, v___x_985_);
v___x_988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
return v___x_988_;
}
}
}
else
{
lean_object* v___x_989_; 
lean_dec_ref(v_repo_964_);
lean_dec_ref(v_remote_963_);
v___x_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_989_, 0, v_rev_962_);
lean_ctor_set(v___x_989_, 1, v_a_965_);
return v___x_989_;
}
v___jp_967_:
{
lean_object* v___x_970_; 
v___x_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_970_, 0, v_rev_968_);
lean_ctor_set(v___x_970_, 1, v___y_969_);
return v___x_970_;
}
}
}
LEAN_EXPORT void l_Lake_GitRepo_resolveRemoteRevision_0interp(lean_interpreter_value* stack)
{
lean_object* v_rev_962_ = stack[0].m_obj;
lean_object* v_remote_963_ = stack[1].m_obj;
lean_object* v_repo_964_ = stack[2].m_obj;
lean_object* v_a_965_ = stack[3].m_obj;
lean_object* v_res_990_;
v_res_990_ = l_Lake_GitRepo_resolveRemoteRevision(v_rev_962_, v_remote_963_, v_repo_964_, v_a_965_);
stack->m_obj
 = v_res_990_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___boxed(lean_object* v_rev_991_, lean_object* v_remote_992_, lean_object* v_repo_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lake_GitRepo_resolveRemoteRevision(v_rev_991_, v_remote_992_, v_repo_993_, v_a_994_);
return v_res_996_;
}
}
lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object* v_repo_997_, lean_object* v_rev_x3f_998_, lean_object* v_remote_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v___x_1002_; 
lean_inc_ref(v_remote_999_);
lean_inc_ref(v_repo_997_);
v___x_1002_ = l_Lake_GitRepo_fetch(v_repo_997_, v_remote_999_, v_a_1000_);
if (lean_obj_tag(v___x_1002_) == 0)
{
if (lean_obj_tag(v_rev_x3f_998_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 1);
lean_inc(v_a_1003_);
lean_dec_ref_known(v___x_1002_, 2);
v___x_1004_ = ((lean_object*)(l_Lake_Git_upstreamBranch___closed__0));
v___x_1005_ = l_Lake_GitRepo_resolveRemoteRevision(v___x_1004_, v_remote_999_, v_repo_997_, v_a_1003_);
return v___x_1005_;
}
else
{
lean_object* v_a_1006_; lean_object* v_val_1007_; lean_object* v___x_1008_; 
v_a_1006_ = lean_ctor_get(v___x_1002_, 1);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1002_, 2);
v_val_1007_ = lean_ctor_get(v_rev_x3f_998_, 0);
lean_inc(v_val_1007_);
lean_dec_ref_known(v_rev_x3f_998_, 1);
v___x_1008_ = l_Lake_GitRepo_resolveRemoteRevision(v_val_1007_, v_remote_999_, v_repo_997_, v_a_1006_);
return v___x_1008_;
}
}
else
{
lean_object* v_a_1009_; lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec_ref(v_remote_999_);
lean_dec(v_rev_x3f_998_);
lean_dec_ref(v_repo_997_);
v_a_1009_ = lean_ctor_get(v___x_1002_, 0);
v_a_1010_ = lean_ctor_get(v___x_1002_, 1);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_1002_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_inc(v_a_1009_);
lean_dec(v___x_1002_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1009_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_GitRepo_findRemoteRevision_0interp(lean_interpreter_value* stack)
{
lean_object* v_repo_997_ = stack[0].m_obj;
lean_object* v_rev_x3f_998_ = stack[1].m_obj;
lean_object* v_remote_999_ = stack[2].m_obj;
lean_object* v_a_1000_ = stack[3].m_obj;
lean_object* v_res_1018_;
v_res_1018_ = l_Lake_GitRepo_findRemoteRevision(v_repo_997_, v_rev_x3f_998_, v_remote_999_, v_a_1000_);
stack->m_obj
 = v_res_1018_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision___boxed(lean_object* v_repo_1019_, lean_object* v_rev_x3f_1020_, lean_object* v_remote_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lake_GitRepo_findRemoteRevision(v_repo_1019_, v_rev_x3f_1020_, v_remote_1021_, v_a_1022_);
return v_res_1024_;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__2(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1027_ = ((lean_object*)(l_Lake_GitRepo_branchExists___closed__0));
v___x_1028_ = lean_unsigned_to_nat(3u);
v___x_1029_ = lean_mk_empty_array_with_capacity(v___x_1028_);
v___x_1030_ = lean_array_push(v___x_1029_, v___x_1027_);
return v___x_1030_;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__3(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1031_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_1032_ = lean_obj_once(&l_Lake_GitRepo_branchExists___closed__2, &l_Lake_GitRepo_branchExists___closed__2_once, _init_l_Lake_GitRepo_branchExists___closed__2);
v___x_1033_ = lean_array_push(v___x_1032_, v___x_1031_);
return v___x_1033_;
}
}
uint8_t l_Lake_GitRepo_branchExists(lean_object* v_rev_1034_, lean_object* v_repo_1035_){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; uint8_t v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v___x_1037_ = ((lean_object*)(l_Lake_GitRepo_branchExists___closed__1));
v___x_1038_ = lean_string_append(v___x_1037_, v_rev_1034_);
v___x_1039_ = lean_obj_once(&l_Lake_GitRepo_branchExists___closed__3, &l_Lake_GitRepo_branchExists___closed__3_once, _init_l_Lake_GitRepo_branchExists___closed__3);
v___x_1040_ = lean_array_push(v___x_1039_, v___x_1038_);
v___x_1041_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1042_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1043_, 0, v_repo_1035_);
v___x_1044_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1045_ = 1;
v___x_1046_ = 0;
v___x_1047_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1047_, 0, v___x_1041_);
lean_ctor_set(v___x_1047_, 1, v___x_1042_);
lean_ctor_set(v___x_1047_, 2, v___x_1040_);
lean_ctor_set(v___x_1047_, 3, v___x_1043_);
lean_ctor_set(v___x_1047_, 4, v___x_1044_);
lean_ctor_set_uint8(v___x_1047_, sizeof(void*)*5, v___x_1045_);
lean_ctor_set_uint8(v___x_1047_, sizeof(void*)*5 + 1, v___x_1046_);
v___x_1048_ = l_Lake_testProc(v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_branchExists_0interp(lean_interpreter_value* stack)
{
lean_object* v_rev_1034_ = stack[0].m_obj;
lean_object* v_repo_1035_ = stack[1].m_obj;
uint8_t v_res_1049_;
v_res_1049_ = l_Lake_GitRepo_branchExists(v_rev_1034_, v_repo_1035_);
stack->m_num = v_res_1049_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object* v_rev_1050_, lean_object* v_repo_1051_, lean_object* v_a_1052_){
_start:
{
uint8_t v_res_1053_; lean_object* v_r_1054_; 
v_res_1053_ = l_Lake_GitRepo_branchExists(v_rev_1050_, v_repo_1051_);
lean_dec_ref(v_rev_1050_);
v_r_1054_ = lean_box(v_res_1053_);
return v_r_1054_;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__0(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1055_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__0));
v___x_1056_ = lean_unsigned_to_nat(3u);
v___x_1057_ = lean_mk_empty_array_with_capacity(v___x_1056_);
v___x_1058_ = lean_array_push(v___x_1057_, v___x_1055_);
return v___x_1058_;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__1(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1059_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_1060_ = lean_obj_once(&l_Lake_GitRepo_revisionExists___closed__0, &l_Lake_GitRepo_revisionExists___closed__0_once, _init_l_Lake_GitRepo_revisionExists___closed__0);
v___x_1061_ = lean_array_push(v___x_1060_, v___x_1059_);
return v___x_1061_;
}
}
uint8_t l_Lake_GitRepo_revisionExists(lean_object* v_rev_1062_, lean_object* v_repo_1063_){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; uint8_t v___x_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1065_ = ((lean_object*)(l_Lake_GitRepo_findCommit_x3f___closed__0));
v___x_1066_ = lean_string_append(v_rev_1062_, v___x_1065_);
v___x_1067_ = lean_obj_once(&l_Lake_GitRepo_revisionExists___closed__1, &l_Lake_GitRepo_revisionExists___closed__1_once, _init_l_Lake_GitRepo_revisionExists___closed__1);
v___x_1068_ = lean_array_push(v___x_1067_, v___x_1066_);
v___x_1069_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1070_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1071_, 0, v_repo_1063_);
v___x_1072_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1073_ = 1;
v___x_1074_ = 0;
v___x_1075_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1075_, 0, v___x_1069_);
lean_ctor_set(v___x_1075_, 1, v___x_1070_);
lean_ctor_set(v___x_1075_, 2, v___x_1068_);
lean_ctor_set(v___x_1075_, 3, v___x_1071_);
lean_ctor_set(v___x_1075_, 4, v___x_1072_);
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*5, v___x_1073_);
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*5 + 1, v___x_1074_);
v___x_1076_ = l_Lake_testProc(v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_revisionExists_0interp(lean_interpreter_value* stack)
{
lean_object* v_rev_1062_ = stack[0].m_obj;
lean_object* v_repo_1063_ = stack[1].m_obj;
uint8_t v_res_1077_;
v_res_1077_ = l_Lake_GitRepo_revisionExists(v_rev_1062_, v_repo_1063_);
stack->m_num = v_res_1077_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists___boxed(lean_object* v_rev_1078_, lean_object* v_repo_1079_, lean_object* v_a_1080_){
_start:
{
uint8_t v_res_1081_; lean_object* v_r_1082_; 
v_res_1081_ = l_Lake_GitRepo_revisionExists(v_rev_1078_, v_repo_1079_);
v_r_1082_ = lean_box(v_res_1081_);
return v_r_1082_;
}
}
lean_object* l_Lake_GitRepo_getTags(lean_object* v_repo_1088_){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; uint8_t v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1090_ = lean_box(0);
v___x_1091_ = ((lean_object*)(l_Lake_GitRepo_getTags___closed__1));
v___x_1092_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1093_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1094_, 0, v_repo_1088_);
v___x_1095_ = lean_unsigned_to_nat(0u);
v___x_1096_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1097_ = 1;
v___x_1098_ = 0;
v___x_1099_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1099_, 0, v___x_1092_);
lean_ctor_set(v___x_1099_, 1, v___x_1093_);
lean_ctor_set(v___x_1099_, 2, v___x_1091_);
lean_ctor_set(v___x_1099_, 3, v___x_1094_);
lean_ctor_set(v___x_1099_, 4, v___x_1096_);
lean_ctor_set_uint8(v___x_1099_, sizeof(void*)*5, v___x_1097_);
lean_ctor_set_uint8(v___x_1099_, sizeof(void*)*5 + 1, v___x_1098_);
v___x_1100_ = l_Lake_captureProc_x3f(v___x_1099_);
if (lean_obj_tag(v___x_1100_) == 1)
{
lean_object* v_val_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v_val_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc_n(v_val_1101_, 2);
lean_dec_ref_known(v___x_1100_, 1);
v___x_1102_ = lean_string_utf8_byte_size(v_val_1101_);
v___x_1103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1103_, 0, v_val_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1095_);
lean_ctor_set(v___x_1103_, 2, v___x_1102_);
v___x_1104_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0);
v___x_1105_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v_val_1101_, v___x_1103_, v___x_1102_, v___x_1104_, v___x_1096_);
lean_dec_ref_known(v___x_1103_, 3);
v___x_1106_ = lean_array_to_list(v___x_1105_);
return v___x_1106_;
}
else
{
lean_dec(v___x_1100_);
return v___x_1090_;
}
}
}
LEAN_EXPORT void l_Lake_GitRepo_getTags_0interp(lean_interpreter_value* stack)
{
lean_object* v_repo_1088_ = stack[0].m_obj;
lean_object* v_res_1107_;
v_res_1107_ = l_Lake_GitRepo_getTags(v_repo_1088_);
stack->m_obj
 = v_res_1107_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags___boxed(lean_object* v_repo_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lake_GitRepo_getTags(v_repo_1108_);
return v_res_1110_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__2(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1113_ = ((lean_object*)(l_Lake_GitRepo_findTag_x3f___closed__0));
v___x_1114_ = lean_unsigned_to_nat(4u);
v___x_1115_ = lean_mk_empty_array_with_capacity(v___x_1114_);
v___x_1116_ = lean_array_push(v___x_1115_, v___x_1113_);
return v___x_1116_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__3(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
v___x_1118_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__2, &l_Lake_GitRepo_findTag_x3f___closed__2_once, _init_l_Lake_GitRepo_findTag_x3f___closed__2);
v___x_1119_ = lean_array_push(v___x_1118_, v___x_1117_);
return v___x_1119_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__4(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1120_ = ((lean_object*)(l_Lake_GitRepo_findTag_x3f___closed__1));
v___x_1121_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__3, &l_Lake_GitRepo_findTag_x3f___closed__3_once, _init_l_Lake_GitRepo_findTag_x3f___closed__3);
v___x_1122_ = lean_array_push(v___x_1121_, v___x_1120_);
return v___x_1122_;
}
}
lean_object* l_Lake_GitRepo_findTag_x3f(lean_object* v_rev_1123_, lean_object* v_repo_1124_){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; uint8_t v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1126_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__4, &l_Lake_GitRepo_findTag_x3f___closed__4_once, _init_l_Lake_GitRepo_findTag_x3f___closed__4);
v___x_1127_ = lean_array_push(v___x_1126_, v_rev_1123_);
v___x_1128_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1129_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1130_, 0, v_repo_1124_);
v___x_1131_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1132_ = 1;
v___x_1133_ = 0;
v___x_1134_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1134_, 0, v___x_1128_);
lean_ctor_set(v___x_1134_, 1, v___x_1129_);
lean_ctor_set(v___x_1134_, 2, v___x_1127_);
lean_ctor_set(v___x_1134_, 3, v___x_1130_);
lean_ctor_set(v___x_1134_, 4, v___x_1131_);
lean_ctor_set_uint8(v___x_1134_, sizeof(void*)*5, v___x_1132_);
lean_ctor_set_uint8(v___x_1134_, sizeof(void*)*5 + 1, v___x_1133_);
v___x_1135_ = l_Lake_captureProc_x3f(v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_findTag_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_rev_1123_ = stack[0].m_obj;
lean_object* v_repo_1124_ = stack[1].m_obj;
lean_object* v_res_1136_;
v_res_1136_ = l_Lake_GitRepo_findTag_x3f(v_rev_1123_, v_repo_1124_);
stack->m_obj
 = v_res_1136_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f___boxed(lean_object* v_rev_1137_, lean_object* v_repo_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lake_GitRepo_findTag_x3f(v_rev_1137_, v_repo_1138_);
return v_res_1140_;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1143_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__0));
v___x_1144_ = lean_unsigned_to_nat(3u);
v___x_1145_ = lean_mk_empty_array_with_capacity(v___x_1144_);
v___x_1146_ = lean_array_push(v___x_1145_, v___x_1143_);
return v___x_1146_;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1147_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__1));
v___x_1148_ = lean_obj_once(&l_Lake_GitRepo_getRemoteUrl_x3f___closed__2, &l_Lake_GitRepo_getRemoteUrl_x3f___closed__2_once, _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2);
v___x_1149_ = lean_array_push(v___x_1148_, v___x_1147_);
return v___x_1149_;
}
}
lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object* v_remote_1150_, lean_object* v_repo_1151_){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; uint8_t v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1153_ = lean_obj_once(&l_Lake_GitRepo_getRemoteUrl_x3f___closed__3, &l_Lake_GitRepo_getRemoteUrl_x3f___closed__3_once, _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3);
v___x_1154_ = lean_array_push(v___x_1153_, v_remote_1150_);
v___x_1155_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1156_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1157_, 0, v_repo_1151_);
v___x_1158_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1159_ = 1;
v___x_1160_ = 0;
v___x_1161_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1161_, 0, v___x_1155_);
lean_ctor_set(v___x_1161_, 1, v___x_1156_);
lean_ctor_set(v___x_1161_, 2, v___x_1154_);
lean_ctor_set(v___x_1161_, 3, v___x_1157_);
lean_ctor_set(v___x_1161_, 4, v___x_1158_);
lean_ctor_set_uint8(v___x_1161_, sizeof(void*)*5, v___x_1159_);
lean_ctor_set_uint8(v___x_1161_, sizeof(void*)*5 + 1, v___x_1160_);
v___x_1162_ = l_Lake_captureProc_x3f(v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_getRemoteUrl_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_remote_1150_ = stack[0].m_obj;
lean_object* v_repo_1151_ = stack[1].m_obj;
lean_object* v_res_1163_;
v_res_1163_ = l_Lake_GitRepo_getRemoteUrl_x3f(v_remote_1150_, v_repo_1151_);
stack->m_obj
 = v_res_1163_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___boxed(lean_object* v_remote_1164_, lean_object* v_repo_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lake_GitRepo_getRemoteUrl_x3f(v_remote_1164_, v_repo_1165_);
return v_res_1167_;
}
}
static lean_object* _init_l_Lake_GitRepo_addRemote___closed__0(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1168_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__0));
v___x_1169_ = lean_unsigned_to_nat(4u);
v___x_1170_ = lean_mk_empty_array_with_capacity(v___x_1169_);
v___x_1171_ = lean_array_push(v___x_1170_, v___x_1168_);
return v___x_1171_;
}
}
static lean_object* _init_l_Lake_GitRepo_addRemote___closed__1(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__1));
v___x_1173_ = lean_obj_once(&l_Lake_GitRepo_addRemote___closed__0, &l_Lake_GitRepo_addRemote___closed__0_once, _init_l_Lake_GitRepo_addRemote___closed__0);
v___x_1174_ = lean_array_push(v___x_1173_, v___x_1172_);
return v___x_1174_;
}
}
lean_object* l_Lake_GitRepo_addRemote(lean_object* v_remote_1175_, lean_object* v_url_1176_, lean_object* v_repo_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; uint8_t v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1180_ = lean_obj_once(&l_Lake_GitRepo_addRemote___closed__1, &l_Lake_GitRepo_addRemote___closed__1_once, _init_l_Lake_GitRepo_addRemote___closed__1);
v___x_1181_ = lean_array_push(v___x_1180_, v_remote_1175_);
v___x_1182_ = lean_array_push(v___x_1181_, v_url_1176_);
v___x_1183_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1184_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1185_, 0, v_repo_1177_);
v___x_1186_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1187_ = 1;
v___x_1188_ = 0;
v___x_1189_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1189_, 0, v___x_1183_);
lean_ctor_set(v___x_1189_, 1, v___x_1184_);
lean_ctor_set(v___x_1189_, 2, v___x_1182_);
lean_ctor_set(v___x_1189_, 3, v___x_1185_);
lean_ctor_set(v___x_1189_, 4, v___x_1186_);
lean_ctor_set_uint8(v___x_1189_, sizeof(void*)*5, v___x_1187_);
lean_ctor_set_uint8(v___x_1189_, sizeof(void*)*5 + 1, v___x_1188_);
v___x_1190_ = lean_box(0);
v___x_1191_ = l_Lake_proc(v___x_1189_, v___x_1187_, v___x_1190_, v_a_1178_);
return v___x_1191_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_addRemote_0interp(lean_interpreter_value* stack)
{
lean_object* v_remote_1175_ = stack[0].m_obj;
lean_object* v_url_1176_ = stack[1].m_obj;
lean_object* v_repo_1177_ = stack[2].m_obj;
lean_object* v_a_1178_ = stack[3].m_obj;
lean_object* v_res_1192_;
v_res_1192_ = l_Lake_GitRepo_addRemote(v_remote_1175_, v_url_1176_, v_repo_1177_, v_a_1178_);
stack->m_obj
 = v_res_1192_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_addRemote___boxed(lean_object* v_remote_1193_, lean_object* v_url_1194_, lean_object* v_repo_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lake_GitRepo_addRemote(v_remote_1193_, v_url_1194_, v_repo_1195_, v_a_1196_);
return v_res_1198_;
}
}
static lean_object* _init_l_Lake_GitRepo_setRemoteUrl___closed__1(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1200_ = ((lean_object*)(l_Lake_GitRepo_setRemoteUrl___closed__0));
v___x_1201_ = lean_obj_once(&l_Lake_GitRepo_addRemote___closed__0, &l_Lake_GitRepo_addRemote___closed__0_once, _init_l_Lake_GitRepo_addRemote___closed__0);
v___x_1202_ = lean_array_push(v___x_1201_, v___x_1200_);
return v___x_1202_;
}
}
lean_object* l_Lake_GitRepo_setRemoteUrl(lean_object* v_remote_1203_, lean_object* v_url_1204_, lean_object* v_repo_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; uint8_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1208_ = lean_obj_once(&l_Lake_GitRepo_setRemoteUrl___closed__1, &l_Lake_GitRepo_setRemoteUrl___closed__1_once, _init_l_Lake_GitRepo_setRemoteUrl___closed__1);
v___x_1209_ = lean_array_push(v___x_1208_, v_remote_1203_);
v___x_1210_ = lean_array_push(v___x_1209_, v_url_1204_);
v___x_1211_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1212_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1213_, 0, v_repo_1205_);
v___x_1214_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1215_ = 1;
v___x_1216_ = 0;
v___x_1217_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1217_, 0, v___x_1211_);
lean_ctor_set(v___x_1217_, 1, v___x_1212_);
lean_ctor_set(v___x_1217_, 2, v___x_1210_);
lean_ctor_set(v___x_1217_, 3, v___x_1213_);
lean_ctor_set(v___x_1217_, 4, v___x_1214_);
lean_ctor_set_uint8(v___x_1217_, sizeof(void*)*5, v___x_1215_);
lean_ctor_set_uint8(v___x_1217_, sizeof(void*)*5 + 1, v___x_1216_);
v___x_1218_ = lean_box(0);
v___x_1219_ = l_Lake_proc(v___x_1217_, v___x_1215_, v___x_1218_, v_a_1206_);
return v___x_1219_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_setRemoteUrl_0interp(lean_interpreter_value* stack)
{
lean_object* v_remote_1203_ = stack[0].m_obj;
lean_object* v_url_1204_ = stack[1].m_obj;
lean_object* v_repo_1205_ = stack[2].m_obj;
lean_object* v_a_1206_ = stack[3].m_obj;
lean_object* v_res_1220_;
v_res_1220_ = l_Lake_GitRepo_setRemoteUrl(v_remote_1203_, v_url_1204_, v_repo_1205_, v_a_1206_);
stack->m_obj
 = v_res_1220_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_setRemoteUrl___boxed(lean_object* v_remote_1221_, lean_object* v_url_1222_, lean_object* v_repo_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lake_GitRepo_setRemoteUrl(v_remote_1221_, v_url_1222_, v_repo_1223_, v_a_1224_);
return v_res_1226_;
}
}
lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object* v_remote_1227_, lean_object* v_repo_1228_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lake_GitRepo_getRemoteUrl_x3f(v_remote_1227_, v_repo_1228_);
if (lean_obj_tag(v___x_1230_) == 0)
{
return v___x_1230_;
}
else
{
lean_object* v_val_1231_; lean_object* v___x_1232_; 
v_val_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_val_1231_);
lean_dec_ref_known(v___x_1230_, 1);
v___x_1232_ = l_Lake_Git_filterUrl_x3f(v_val_1231_);
return v___x_1232_;
}
}
}
LEAN_EXPORT void l_Lake_GitRepo_getFilteredRemoteUrl_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_remote_1227_ = stack[0].m_obj;
lean_object* v_repo_1228_ = stack[1].m_obj;
lean_object* v_res_1233_;
v_res_1233_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v_remote_1227_, v_repo_1228_);
stack->m_obj
 = v_res_1233_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f___boxed(lean_object* v_remote_1234_, lean_object* v_repo_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v_remote_1234_, v_repo_1235_);
return v_res_1237_;
}
}
static lean_object* _init_l_Lake_GitRepo_pruneRemote___closed__1(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = ((lean_object*)(l_Lake_GitRepo_pruneRemote___closed__0));
v___x_1240_ = lean_obj_once(&l_Lake_GitRepo_getRemoteUrl_x3f___closed__2, &l_Lake_GitRepo_getRemoteUrl_x3f___closed__2_once, _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2);
v___x_1241_ = lean_array_push(v___x_1240_, v___x_1239_);
return v___x_1241_;
}
}
lean_object* l_Lake_GitRepo_pruneRemote(lean_object* v_remote_1242_, lean_object* v_repo_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1246_ = lean_obj_once(&l_Lake_GitRepo_pruneRemote___closed__1, &l_Lake_GitRepo_pruneRemote___closed__1_once, _init_l_Lake_GitRepo_pruneRemote___closed__1);
v___x_1247_ = lean_array_push(v___x_1246_, v_remote_1242_);
v___x_1248_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1249_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1250_, 0, v_repo_1243_);
v___x_1251_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1252_ = 1;
v___x_1253_ = 0;
v___x_1254_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1254_, 0, v___x_1248_);
lean_ctor_set(v___x_1254_, 1, v___x_1249_);
lean_ctor_set(v___x_1254_, 2, v___x_1247_);
lean_ctor_set(v___x_1254_, 3, v___x_1250_);
lean_ctor_set(v___x_1254_, 4, v___x_1251_);
lean_ctor_set_uint8(v___x_1254_, sizeof(void*)*5, v___x_1252_);
lean_ctor_set_uint8(v___x_1254_, sizeof(void*)*5 + 1, v___x_1253_);
v___x_1255_ = lean_box(0);
v___x_1256_ = l_Lake_proc(v___x_1254_, v___x_1252_, v___x_1255_, v_a_1244_);
return v___x_1256_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_pruneRemote_0interp(lean_interpreter_value* stack)
{
lean_object* v_remote_1242_ = stack[0].m_obj;
lean_object* v_repo_1243_ = stack[1].m_obj;
lean_object* v_a_1244_ = stack[2].m_obj;
lean_object* v_res_1257_;
v_res_1257_ = l_Lake_GitRepo_pruneRemote(v_remote_1242_, v_repo_1243_, v_a_1244_);
stack->m_obj
 = v_res_1257_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_pruneRemote___boxed(lean_object* v_remote_1258_, lean_object* v_repo_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lake_GitRepo_pruneRemote(v_remote_1258_, v_repo_1259_, v_a_1260_);
return v_res_1262_;
}
}
uint8_t l_Lake_GitRepo_hasNoDiff(lean_object* v_repo_1273_){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; uint8_t v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1275_ = ((lean_object*)(l_Lake_GitRepo_hasNoDiff___closed__2));
v___x_1276_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1277_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1278_, 0, v_repo_1273_);
v___x_1279_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1280_ = 1;
v___x_1281_ = 0;
v___x_1282_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1282_, 0, v___x_1276_);
lean_ctor_set(v___x_1282_, 1, v___x_1277_);
lean_ctor_set(v___x_1282_, 2, v___x_1275_);
lean_ctor_set(v___x_1282_, 3, v___x_1278_);
lean_ctor_set(v___x_1282_, 4, v___x_1279_);
lean_ctor_set_uint8(v___x_1282_, sizeof(void*)*5, v___x_1280_);
lean_ctor_set_uint8(v___x_1282_, sizeof(void*)*5 + 1, v___x_1281_);
v___x_1283_ = l_Lake_testProc(v___x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT void l_Lake_GitRepo_hasNoDiff_0interp(lean_interpreter_value* stack)
{
lean_object* v_repo_1273_ = stack[0].m_obj;
uint8_t v_res_1284_;
v_res_1284_ = l_Lake_GitRepo_hasNoDiff(v_repo_1273_);
stack->m_num = v_res_1284_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff___boxed(lean_object* v_repo_1285_, lean_object* v_a_1286_){
_start:
{
uint8_t v_res_1287_; lean_object* v_r_1288_; 
v_res_1287_ = l_Lake_GitRepo_hasNoDiff(v_repo_1285_);
v_r_1288_ = lean_box(v_res_1287_);
return v_r_1288_;
}
}
uint8_t l_Lake_GitRepo_hasDiff(lean_object* v_repo_1289_){
_start:
{
uint8_t v___x_1291_; 
v___x_1291_ = l_Lake_GitRepo_hasNoDiff(v_repo_1289_);
if (v___x_1291_ == 0)
{
uint8_t v___x_1292_; 
v___x_1292_ = 1;
return v___x_1292_;
}
else
{
uint8_t v___x_1293_; 
v___x_1293_ = 0;
return v___x_1293_;
}
}
}
LEAN_EXPORT void l_Lake_GitRepo_hasDiff_0interp(lean_interpreter_value* stack)
{
lean_object* v_repo_1289_ = stack[0].m_obj;
uint8_t v_res_1294_;
v_res_1294_ = l_Lake_GitRepo_hasDiff(v_repo_1289_);
stack->m_num = v_res_1294_;
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff___boxed(lean_object* v_repo_1295_, lean_object* v_a_1296_){
_start:
{
uint8_t v_res_1297_; lean_object* v_r_1298_; 
v_res_1297_ = l_Lake_GitRepo_hasDiff(v_repo_1295_);
v_r_1298_ = lean_box(v_res_1297_);
return v_r_1298_;
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_String(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Git(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Lake_Util_String(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Git(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Git(builtin);
}
#ifdef __cplusplus
}
#endif
