{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRevbindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_monadic_quicksort_verification (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
vbindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

vbindir     = "/Users/henry/.cabal/bin"
libdir     = "/Users/henry/.cabal/lib/x86_64-osx-ghc-8.10.1/monadic-quicksort-verification-0.1.0.0-inplace-monadic-quicksort-verification"
dynlibdir  = "/Users/henry/.cabal/lib/x86_64-osx-ghc-8.10.1"
datadir    = "/Users/henry/.cabal/share/x86_64-osx-ghc-8.10.1/monadic-quicksort-verification-0.1.0.0"
libexecdir = "/Users/henry/.cabal/libexec/x86_64-osx-ghc-8.10.1/monadic-quicksort-verification-0.1.0.0"
sysconfdir = "/Users/henry/.cabal/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "monadic_quicksort_verification_vbindir") (\_ -> return vbindir)
getLibDir = catchIO (getEnv "monadic_quicksort_verification_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "monadic_quicksort_verification_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "monadic_quicksort_verification_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "monadic_quicksort_verification_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "monadic_quicksort_verification_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
