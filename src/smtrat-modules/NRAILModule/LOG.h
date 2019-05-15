
#pragma once

namespace smtrat {
    class LOG : public carl::Singleton<LOG>{
        friend class carl::Singleton<LOG>;

    public:
        bool debugEnabled = false;
        const bool isDebugEnabled() {
            return  debugEnabled;
        }
    };
}