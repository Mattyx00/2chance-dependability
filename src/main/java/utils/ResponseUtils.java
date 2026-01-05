package utils;

import javax.servlet.http.HttpServletResponse;
import java.io.IOException;

public class ResponseUtils {

    private ResponseUtils() {
        // Utility class
    }

    public static void sendError(HttpServletResponse response, int statusCode) {
        sendError(response, statusCode, null);
    }

    public static void sendError(HttpServletResponse response, int statusCode, String message) {
        if (!response.isCommitted()) {
            try {
                if (message == null) {
                    response.sendError(statusCode);
                } else {
                    response.sendError(statusCode, message);
                }
            } catch (IOException e) {
                // Log exception here if a logger is available
                e.printStackTrace();
            }
        }
    }
}
