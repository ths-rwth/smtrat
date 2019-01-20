
#pragma once

namespace smtrat {
    class LOG : public carl::Singleton<LOG>{
        friend class carl::Singleton<LOG>;

    public:
        bool debugEnabled = true;
        const bool isDebugEnabled() {
            return  debugEnabled;
        }
    };
}