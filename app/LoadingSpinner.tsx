import React from "react";

const LoadingSpinner = () => {
  return (
    <div className="fixed inset-0 flex items-center justify-center bg-black bg-opacity-30 z-50">
      <div className="animate-spin rounded-full h-16 w-16 border-t-4 border-yellow-500 text-blue-500">
        __ Z3...
      </div>
    </div>
  );
};

export default LoadingSpinner;
