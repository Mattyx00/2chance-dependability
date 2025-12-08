# Stage 1: Build the application
FROM maven:3.9-eclipse-temurin-19 AS build

WORKDIR /app

# Copy pom.xml and download dependencies
COPY pom.xml .
# Go offline to cache dependencies (optional but good practice, though might fail if some deps are missing in repo)
# simpler to just copy everything and build.
# RUN mvn dependency:go-offline

# Copy source code
COPY src ./src

# Build the WAR file, skipping tests as requested/necessary due to compilation errors
RUN mvn clean package -Dmaven.test.skip=true

# Stage 2: Run the application
FROM tomcat:9.0

# Remove default webapps
RUN rm -rf /usr/local/tomcat/webapps/*

# Copy the WAR file from the build stage
COPY --from=build /app/target/2chance-1.0-SNAPSHOT.war /usr/local/tomcat/webapps/ROOT.war

# Copy the upload directory
# Note: In a multi-stage build, we need to copy 'upload' from the build context (the project root), 
# not from the build stage image (unless we copied it there first).
# The 'COPY' command in the final stage uses the build context by default unless --from is specified.
COPY upload /usr/local/tomcat/upload

# Expose port 8080
EXPOSE 8080

CMD ["catalina.sh", "run"]
